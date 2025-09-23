"""Word Merger GUI application.

This tool scans Daily Notes folders, allows the operator to select a client
and date range (or drag-and-drop arbitrary files), and combines the selected
Word documents into a single anonymised `.docx` output.
"""
from __future__ import annotations

import os
import re
import sys
import threading
import queue
from copy import deepcopy
from dataclasses import dataclass
from datetime import date, datetime
from pathlib import Path
from typing import Iterable, List, Optional, Sequence, Tuple

try:
    from tkinter import filedialog, messagebox
    import tkinter as tk
    from tkinter import ttk
    from tkinter.scrolledtext import ScrolledText
except ImportError as exc:  # pragma: no cover - tkinter is part of stdlib but guard just in case
    raise RuntimeError("tkinter is required to run this application") from exc

# Optional drag-and-drop support ------------------------------------------------
try:  # pragma: no cover - import guarded for environments lacking tkdnd
    from tkinterdnd2 import DND_FILES, TkinterDnD
except Exception:  # pragma: no cover - we fall back to normal Tk when tkdnd is missing
    DND_FILES = None
    TkBase = tk.Tk
else:  # pragma: no cover - executed when tkinterdnd2 is available
    class TkBase(TkinterDnD.Tk):
        """Custom base Tk class using tkinterdnd2 when installed."""
        pass

from tkcalendar import DateEntry
from docx import Document

APP_NAME = "Word Merger"
CONFIG_VENDOR = "WordMerger"
NAMES_FILENAME = "names.txt"
DEFAULT_NAMES_RESOURCE = Path(__file__).with_name("default_names.txt")

DOCX_PATTERN = re.compile(r"^(?P<day>\d{2})\.(?P<month>\d{2})\.(?P<year>\d{4})\.docx$", re.IGNORECASE)


@dataclass(frozen=True)
class FileEntry:
    path: Path
    file_date: Optional[date]  # None when we cannot parse a date from the filename


class NameAnonymizer:
    """Implements the name replacement logic shared with the reference app."""

    def __init__(self, names: Iterable[str] | None = None) -> None:
        self._names: set[str] = set()
        if names:
            self._names = {n.strip() for n in names if n.strip()}

    # ------------------------------------------------------------------
    @property
    def names(self) -> set[str]:
        return set(self._names)

    # ------------------------------------------------------------------
    def update_names(self, new_names: Iterable[str]) -> None:
        self._names = {n.strip() for n in new_names if n.strip()}

    # ------------------------------------------------------------------
    def anonymize_text(self, text: str) -> str:
        processed = text
        # Replace longer names first to avoid partial matches overriding full ones.
        for name in sorted(self._names, key=len, reverse=True):
            pattern = r"\\b" + re.escape(name) + r"(?P<suffix>(?:['’]s)|s(?:['’])?)?\\b"

            def repl(match: re.Match[str]) -> str:
                suffix = match.group("suffix") or ""
                if suffix in ("'s", "’s"):
                    return "service user's"
                if suffix.startswith("s"):
                    if len(suffix) > 1 and suffix[1] in ("'", "’"):
                        return "service users" + suffix[1]
                    return "service users"
                return "service user"

            processed = re.sub(pattern, repl, processed, flags=re.IGNORECASE)
        return processed


class WordMergerApp:
    """Main GUI application."""

    def __init__(self) -> None:
        self.root = TkBase()
        self.root.title(APP_NAME)
        self.root.geometry("1100x750")

        self._log_queue: "queue.Queue[tuple[str, tuple]]" = queue.Queue()
        self._worker_thread: Optional[threading.Thread] = None

        self.root_dir = tk.StringVar()
        self.client_var = tk.StringVar()
        self.month_var = tk.StringVar(value="All Months")

        self.manual_files: list[Path] = []
        self.auto_files: list[FileEntry] = []
        self.manual_mode = False

        self.names_file = self._ensure_names_file()
        self.anonymizer = NameAnonymizer(self._load_names())

        self.month_map: dict[str, list[Path]] = {"All Months": []}

        self._build_gui()
        self.root.after(200, self._process_queue)

    # ------------------------------------------------------------------
    def _build_gui(self) -> None:
        self._build_path_section()
        self._build_selection_section()
        self._build_date_section()
        self._build_dragdrop_section()
        self._build_files_preview()
        self._build_names_section()
        self._build_progress_section()
        self._build_log_section()
        self._build_action_section()

    # ------------------------------------------------------------------
    def _build_path_section(self) -> None:
        frame = ttk.LabelFrame(self.root, text="Root Daily Notes Folder", padding=10)
        frame.pack(fill="x", padx=12, pady=(10, 6))

        entry = ttk.Entry(frame, textvariable=self.root_dir)
        entry.pack(side=tk.LEFT, fill="x", expand=True, padx=(0, 6))
        entry.bind("<FocusOut>", lambda _e: self._refresh_clients())

        ttk.Button(frame, text="Browse…", command=self._browse_root).pack(side=tk.LEFT)
        ttk.Button(frame, text="Reload", command=self._refresh_clients).pack(side=tk.LEFT, padx=(6, 0))

    # ------------------------------------------------------------------
    def _build_selection_section(self) -> None:
        frame = ttk.LabelFrame(self.root, text="Client and Month", padding=10)
        frame.pack(fill="x", padx=12, pady=6)

        ttk.Label(frame, text="Client:").pack(side=tk.LEFT)
        self.client_combo = ttk.Combobox(frame, textvariable=self.client_var, state="readonly", width=40)
        self.client_combo.pack(side=tk.LEFT, padx=(6, 12), fill="x", expand=True)
        self.client_combo.bind("<<ComboboxSelected>>", lambda _e: self._refresh_months())

        ttk.Label(frame, text="Month:").pack(side=tk.LEFT)
        self.month_combo = ttk.Combobox(frame, textvariable=self.month_var, state="readonly", width=28)
        self.month_combo.pack(side=tk.LEFT, padx=(6, 12))
        self.month_combo.bind("<<ComboboxSelected>>", lambda _e: self._update_dates_from_selection())

    # ------------------------------------------------------------------
    def _build_date_section(self) -> None:
        frame = ttk.LabelFrame(self.root, text="Date Range (auto selection)", padding=10)
        frame.pack(fill="x", padx=12, pady=6)

        ttk.Label(frame, text="Start:").pack(side=tk.LEFT)
        self.start_date = DateEntry(frame, width=12, date_pattern="dd/mm/yyyy")
        self.start_date.pack(side=tk.LEFT, padx=(6, 12))
        self.start_date.bind("<<DateEntrySelected>>", lambda _e: self._refresh_auto_files())

        ttk.Label(frame, text="End:").pack(side=tk.LEFT)
        self.end_date = DateEntry(frame, width=12, date_pattern="dd/mm/yyyy")
        self.end_date.pack(side=tk.LEFT, padx=(6, 12))
        self.end_date.bind("<<DateEntrySelected>>", lambda _e: self._refresh_auto_files())

        ttk.Label(frame, text="Auto selection scans matching .docx names in the chosen folder.").pack(side=tk.LEFT)

    # ------------------------------------------------------------------
    def _build_dragdrop_section(self) -> None:
        frame = ttk.LabelFrame(self.root, text="Manual Selection (drag files here or use Add button)", padding=10)
        frame.pack(fill="x", padx=12, pady=6)

        drop_frame = tk.Frame(frame, height=80, relief=tk.RIDGE, borderwidth=2, bg="#fafafa")
        drop_frame.pack(fill="x", expand=True)

        instructions = tk.Label(
            drop_frame,
            text=(
                "Drop .docx files here to override auto-selection.\n"
                "You can mix files from different folders."
            ),
            justify=tk.CENTER,
            bg="#fafafa",
        )
        instructions.pack(expand=True, fill="both")

        if DND_FILES is not None:
            drop_frame.drop_target_register(DND_FILES)
            drop_frame.dnd_bind("<Drop>", self._on_drop_files)
        else:
            instructions.config(text=(
                "tkinterdnd2 is not installed; drag-and-drop disabled.\n"
                "Use the Add Files button instead."
            ))

        buttons = tk.Frame(frame)
        buttons.pack(fill="x", pady=(8, 0))
        ttk.Button(buttons, text="Add Files…", command=self._add_files_dialog).pack(side=tk.LEFT)
        ttk.Button(buttons, text="Clear Manual Selection", command=self._clear_manual_selection).pack(side=tk.LEFT, padx=8)
        self.manual_mode_label = ttk.Label(buttons, text="Auto-selection active", foreground="#1b5e20")
        self.manual_mode_label.pack(side=tk.LEFT, padx=12)

    # ------------------------------------------------------------------
    def _build_files_preview(self) -> None:
        frame = ttk.LabelFrame(self.root, text="Files to Merge", padding=10)
        frame.pack(fill="both", padx=12, pady=6, expand=True)

        self.files_listbox = tk.Listbox(frame, height=10)
        self.files_listbox.pack(side=tk.LEFT, fill="both", expand=True)

        scrollbar = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=self.files_listbox.yview)
        scrollbar.pack(side=tk.RIGHT, fill="y")
        self.files_listbox.config(yscrollcommand=scrollbar.set)

    # ------------------------------------------------------------------
    def _build_names_section(self) -> None:
        frame = ttk.LabelFrame(self.root, text="Names to Anonymise", padding=10)
        frame.pack(fill="x", padx=12, pady=6)

        entry_frame = tk.Frame(frame)
        entry_frame.pack(fill="x")

        ttk.Label(entry_frame, text="Add name:").pack(side=tk.LEFT)
        self.new_name_var = tk.StringVar()
        new_name_entry = ttk.Entry(entry_frame, textvariable=self.new_name_var, width=30)
        new_name_entry.pack(side=tk.LEFT, padx=(6, 6))

        ttk.Button(entry_frame, text="Add", command=self._add_name).pack(side=tk.LEFT)
        ttk.Button(entry_frame, text="Remove Selected", command=self._remove_selected_name).pack(side=tk.LEFT, padx=(6, 0))

        self.names_listbox = tk.Listbox(frame, height=6)
        self.names_listbox.pack(fill="x", pady=(8, 0))
        self._refresh_names_listbox()

    # ------------------------------------------------------------------
    def _build_progress_section(self) -> None:
        frame = ttk.Frame(self.root, padding=(12, 0))
        frame.pack(fill="x", pady=6)
        ttk.Label(frame, text="Progress:").pack(side=tk.LEFT)
        self.progress = ttk.Progressbar(frame, length=300, mode="determinate")
        self.progress.pack(side=tk.LEFT, padx=(6, 12), fill="x", expand=True)
        self.status_var = tk.StringVar(value="Idle")
        ttk.Label(frame, textvariable=self.status_var).pack(side=tk.LEFT)

    # ------------------------------------------------------------------
    def _build_log_section(self) -> None:
        frame = ttk.LabelFrame(self.root, text="Log", padding=10)
        frame.pack(fill="both", padx=12, pady=6, expand=True)
        self.log_text = ScrolledText(frame, height=10, wrap=tk.WORD, state="disabled")
        self.log_text.pack(fill="both", expand=True)

    # ------------------------------------------------------------------
    def _build_action_section(self) -> None:
        frame = ttk.Frame(self.root, padding=12)
        frame.pack(fill="x", pady=(0, 12))
        self.start_button = ttk.Button(frame, text="Create Combined Document", command=self._start_merge)
        self.start_button.pack(side=tk.LEFT)

    # ------------------------------------------------------------------
    def _browse_root(self) -> None:
        selected = filedialog.askdirectory(title="Select Daily Notes Root")
        if selected:
            self.root_dir.set(selected)
            self._refresh_clients()

    # ------------------------------------------------------------------
    def _refresh_clients(self) -> None:
        root_path = Path(self.root_dir.get()).expanduser()
        clients: list[str] = []
        if root_path.is_dir():
            for child in sorted(root_path.iterdir()):
                if child.is_dir():
                    clients.append(child.name)
        self.client_combo["values"] = clients
        if clients:
            if self.client_var.get() not in clients:
                self.client_var.set(clients[0])
            self._refresh_months()
        else:
            self.client_var.set("")
            self.month_combo["values"] = ["All Months"]
            self.month_var.set("All Months")
            self.month_map = {"All Months": []}
            self._refresh_auto_files()

    # ------------------------------------------------------------------
    def _refresh_months(self) -> None:
        self.month_map = {"All Months": []}
        root_path = Path(self.root_dir.get()).expanduser()
        client = self.client_var.get()
        client_path = root_path / client if client else None
        months: list[str] = []
        if client_path and client_path.is_dir():
            for child in sorted(client_path.iterdir()):
                if child.is_dir():
                    months.append(child.name)
                    self.month_map.setdefault(child.name, []).append(child)
                    self.month_map["All Months"].append(child)
        if not months:
            months = []
        values = ["All Months"] + months
        self.month_combo["values"] = values
        if self.month_var.get() not in values:
            self.month_var.set(values[0] if values else "All Months")
        self._update_dates_from_selection()

    # ------------------------------------------------------------------
    def _update_dates_from_selection(self) -> None:
        selected_month = self.month_var.get()
        folders = self.month_map.get(selected_month, [])
        file_dates: list[date] = []
        for folder in folders:
            for file in folder.glob("*.docx"):
                match = DOCX_PATTERN.match(file.name)
                if match:
                    file_dates.append(date(int(match.group("year")), int(match.group("month")), int(match.group("day"))))
        if file_dates:
            min_date = min(file_dates)
            max_date = max(file_dates)
        else:
            today = date.today()
            min_date = today
            max_date = today

        for widget in (self.start_date, self.end_date):
            widget.config(mindate=min_date, maxdate=max_date)
        self.start_date.set_date(min_date)
        self.end_date.set_date(max_date)
        self._refresh_auto_files()

    # ------------------------------------------------------------------
    def _refresh_auto_files(self) -> None:
        start = self.start_date.get_date()
        end = self.end_date.get_date()
        if start > end:
            start, end = end, start
            self.start_date.set_date(start)
            self.end_date.set_date(end)

        folders = self.month_map.get(self.month_var.get(), [])
        entries: list[FileEntry] = []
        for folder in folders:
            for file in sorted(folder.glob("*.docx")):
                match = DOCX_PATTERN.match(file.name)
                file_date: Optional[date] = None
                if match:
                    file_date = date(int(match.group("year")), int(match.group("month")), int(match.group("day")))
                if file_date and (start <= file_date <= end):
                    entries.append(FileEntry(file, file_date))
        entries.sort(key=lambda item: (item.file_date or date.min, item.path.name.lower()))
        self.auto_files = entries
        if not self.manual_mode:
            self._display_files([entry.path for entry in self.auto_files])

    # ------------------------------------------------------------------
    def _on_drop_files(self, event: tk.Event) -> None:  # pragma: no cover - GUI interaction
        paths = self.root.tk.splitlist(event.data)
        self._add_manual_files(paths)

    # ------------------------------------------------------------------
    def _add_files_dialog(self) -> None:  # pragma: no cover - GUI interaction
        filepaths = filedialog.askopenfilenames(
            title="Select Word documents",
            filetypes=[("Word documents", "*.docx")],
        )
        if filepaths:
            self._add_manual_files(filepaths)

    # ------------------------------------------------------------------
    def _add_manual_files(self, paths: Sequence[str | os.PathLike[str]]) -> None:
        added = 0
        for raw_path in paths:
            path = Path(raw_path)
            if path.suffix.lower() != ".docx" or not path.exists():
                continue
            if path not in self.manual_files:
                self.manual_files.append(path)
                added += 1
        if added:
            self.manual_mode = True
            self._display_files(self.manual_files)
            self.manual_mode_label.config(text="Manual selection overrides auto", foreground="#b71c1c")
        elif not self.manual_files:
            self._clear_manual_selection()

    # ------------------------------------------------------------------
    def _clear_manual_selection(self) -> None:
        self.manual_files.clear()
        self.manual_mode = False
        self.manual_mode_label.config(text="Auto-selection active", foreground="#1b5e20")
        self._display_files([entry.path for entry in self.auto_files])

    # ------------------------------------------------------------------
    def _display_files(self, paths: Sequence[Path]) -> None:
        self.files_listbox.delete(0, tk.END)
        for path in paths:
            self.files_listbox.insert(tk.END, str(path))
        count = len(paths)
        self.status_var.set(f"{count} file{'s' if count != 1 else ''} queued")

    # ------------------------------------------------------------------
    def _add_name(self) -> None:
        name = self.new_name_var.get().strip()
        if not name:
            messagebox.showwarning(APP_NAME, "Enter a name to add.")
            return
        names = self.anonymizer.names
        if name in names:
            messagebox.showinfo(APP_NAME, f"'{name}' is already listed.")
            return
        names.add(name)
        self.anonymizer.update_names(names)
        self._save_names()
        self.new_name_var.set("")
        self._refresh_names_listbox()

    # ------------------------------------------------------------------
    def _remove_selected_name(self) -> None:
        selected = self.names_listbox.curselection()
        if not selected:
            messagebox.showwarning(APP_NAME, "Select a name to remove.")
            return
        index = selected[0]
        name = self.names_listbox.get(index)
        names = self.anonymizer.names
        if name in names:
            names.remove(name)
            self.anonymizer.update_names(names)
            self._save_names()
            self._refresh_names_listbox()

    # ------------------------------------------------------------------
    def _refresh_names_listbox(self) -> None:
        self.names_listbox.delete(0, tk.END)
        for name in sorted(self.anonymizer.names, key=str.lower):
            self.names_listbox.insert(tk.END, name)

    # ------------------------------------------------------------------
    def _start_merge(self) -> None:
        if self._worker_thread and self._worker_thread.is_alive():
            messagebox.showinfo(APP_NAME, "Processing already in progress.")
            return

        files: list[Path]
        if self.manual_mode and self.manual_files:
            files = list(self.manual_files)
        else:
            files = [entry.path for entry in self.auto_files]

        if not files:
            messagebox.showwarning(APP_NAME, "No files selected for merging.")
            return

        start, end = self._calculate_range_from_files(files)
        default_name = self._build_default_output_name(start, end)
        output_path = filedialog.asksaveasfilename(
            title="Save combined document",
            defaultextension=".docx",
            filetypes=[("Word document", "*.docx")],
            initialfile=default_name,
        )
        if not output_path:
            return

        self.progress.config(maximum=len(files), value=0)
        self.status_var.set("Processing…")
        self.start_button.config(state=tk.DISABLED)
        self._set_log_state(clear=True)
        self._log("Starting merge of %d file(s)…" % len(files))

        self._worker_thread = threading.Thread(
            target=self._merge_worker,
            args=(files, Path(output_path)),
            daemon=True,
        )
        self._worker_thread.start()

    # ------------------------------------------------------------------
    def _merge_worker(self, files: Sequence[Path], output_path: Path) -> None:
        success = False
        try:
            combined_doc = Document()
            # Remove the initial empty paragraph
            if combined_doc.paragraphs:
                p = combined_doc.paragraphs[0]._element
                p.getparent().remove(p)

            for index, file_path in enumerate(files, start=1):
                self._queue_message("log", (f"Processing {file_path}",))
                src_doc = Document(str(file_path))
                self._apply_anonymisation(src_doc)
                if len(combined_doc.element.body):
                    combined_doc.add_page_break()
                self._append_document(combined_doc, src_doc)
                self._queue_message("progress", (index, len(files)))

            # Final anonymisation pass on the merged document
            self._apply_anonymisation(combined_doc)
            combined_doc.save(str(output_path))
            success = True
            self._queue_message("log", (f"Saved combined document to {output_path}",))
        except Exception as exc:
            self._queue_message("log", (f"Error: {exc}",))
            self._queue_message("error", (str(exc),))
        finally:
            self._queue_message("done", (success, output_path))

    # ------------------------------------------------------------------
    def _apply_anonymisation(self, doc: Document) -> None:
        for paragraph in doc.paragraphs:
            self._anonymise_paragraph(paragraph)
        for table in doc.tables:
            for row in table.rows:
                for cell in row.cells:
                    for paragraph in cell.paragraphs:
                        self._anonymise_paragraph(paragraph)

    # ------------------------------------------------------------------
    def _anonymise_paragraph(self, paragraph) -> None:
        text = paragraph.text
        if not text:
            return
        replaced = self.anonymizer.anonymize_text(text)
        if replaced == text:
            return
        if paragraph.runs:
            paragraph.runs[0].text = replaced
            for run in paragraph.runs[1:]:
                run.text = ""
        else:
            paragraph.text = replaced

    # ------------------------------------------------------------------
    def _append_document(self, destination: Document, source: Document) -> None:
        for element in source.element.body:
            destination.element.body.append(deepcopy(element))

    # ------------------------------------------------------------------
    def _set_log_state(self, clear: bool = False) -> None:
        self.log_text.config(state="normal")
        if clear:
            self.log_text.delete("1.0", tk.END)
        self.log_text.config(state="disabled")

    # ------------------------------------------------------------------
    def _log(self, message: str) -> None:
        self.log_text.config(state="normal")
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.log_text.insert(tk.END, f"[{timestamp}] {message}\n")
        self.log_text.see(tk.END)
        self.log_text.config(state="disabled")

    # ------------------------------------------------------------------
    def _queue_message(self, kind: str, payload: tuple) -> None:
        self._log_queue.put((kind, payload))

    # ------------------------------------------------------------------
    def _process_queue(self) -> None:
        try:
            while True:
                kind, payload = self._log_queue.get_nowait()
                if kind == "log":
                    (message,) = payload
                    self._log(message)
                elif kind == "progress":
                    current, total = payload
                    self.progress.config(maximum=total, value=current)
                    self.status_var.set(f"{current}/{total} completed")
                elif kind == "error":
                    (message,) = payload
                    messagebox.showerror(APP_NAME, message)
                elif kind == "done":
                    success, output_path = payload
                    self.start_button.config(state=tk.NORMAL)
                    if success:
                        self.status_var.set("Done")
                        messagebox.showinfo(APP_NAME, f"Combined document saved to:\n{output_path}")
                    else:
                        self.status_var.set("Failed")
                self._log_queue.task_done()
        except queue.Empty:
            pass
        finally:
            self.root.after(200, self._process_queue)

    # ------------------------------------------------------------------
    def _calculate_range_from_files(self, files: Sequence[Path]) -> Tuple[Optional[date], Optional[date]]:
        dates: list[date] = []
        for path in files:
            match = DOCX_PATTERN.match(path.name)
            if match:
                try:
                    file_date = date(int(match.group("year")), int(match.group("month")), int(match.group("day")))
                    dates.append(file_date)
                except ValueError:
                    continue
        if not dates:
            return None, None
        return min(dates), max(dates)

    # ------------------------------------------------------------------
    def _build_default_output_name(self, start: Optional[date], end: Optional[date]) -> str:
        if start and end:
            if start == end:
                label = start.strftime("%d.%m.%Y")
            else:
                label = f"{start:%d.%m.%Y} to {end:%d.%m.%Y}"
            return f"{label}.docx"
        return "combined.docx"

    # ------------------------------------------------------------------
    def _ensure_names_file(self) -> Path:
        config_dir = self._user_config_dir()
        config_dir.mkdir(parents=True, exist_ok=True)
        names_path = config_dir / NAMES_FILENAME
        if not names_path.exists():
            if DEFAULT_NAMES_RESOURCE.exists():
                names_path.write_text(DEFAULT_NAMES_RESOURCE.read_text(encoding="utf-8"), encoding="utf-8")
            else:
                names_path.write_text("", encoding="utf-8")
        return names_path

    # ------------------------------------------------------------------
    def _user_config_dir(self) -> Path:
        if sys.platform == "win32":
            appdata = os.getenv("APPDATA")
            if appdata:
                return Path(appdata) / CONFIG_VENDOR
        return Path.home() / ".config" / CONFIG_VENDOR

    # ------------------------------------------------------------------
    def _load_names(self) -> List[str]:
        try:
            return self.names_file.read_text(encoding="utf-8").splitlines()
        except Exception:
            messagebox.showwarning(APP_NAME, f"Could not read names file at {self.names_file}")
            return []

    # ------------------------------------------------------------------
    def _save_names(self) -> None:
        try:
            with self.names_file.open("w", encoding="utf-8") as fh:
                for name in sorted(self.anonymizer.names, key=str.lower):
                    fh.write(name + "\n")
        except Exception as exc:
            messagebox.showerror(APP_NAME, f"Unable to save names list: {exc}")

    # ------------------------------------------------------------------
    def run(self) -> None:
        self.root.mainloop()


def main() -> None:
    app = WordMergerApp()
    app.run()


if __name__ == "__main__":  # pragma: no cover - CLI entry point
    main()
