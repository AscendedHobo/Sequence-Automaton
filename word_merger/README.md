# Word Merger

Desktop utility for combining daily notes Word documents into a single,
anonymised report. The GUI lets you pick a client folder and date range or
drag-and-drop hand-picked files. All selected documents are merged in date
order and processed using the "service user" name replacement logic.

## Features

- Browse to the `DAILY NOTES 2025` root, then choose a client and month folder.
- Pick a start and end date (with a calendar picker) to auto-select matching
  `DD.MM.YYYY.docx` files.
- Drag files from anywhere onto the drop-zone to override the auto-selection.
- Maintain a reusable list of names to anonymise. The list is stored in a
  writable configuration file the first time the app runs.
- Merge the documents, append them into a single `.docx`, and anonymise the
  output once more before saving.
- Progress bar, activity log, and manual output location selection.

## Running the App

```bash
python -m word_merger.app
```

The first launch creates a names file in:

- Windows: `%APPDATA%\WordMerger\names.txt`
- Other platforms: `~/.config/WordMerger/names.txt`

Edit this list within the GUI under **Names to Anonymise**.

## Dependencies

The app relies on these additional Python packages:

- `python-docx`
- `tkcalendar`
- `tkinterdnd2` (optional, enables drag-and-drop)

Install them via the repo-level `requirements.txt` or with `pip install -r
requirements.txt`.
