import tkinter as tk
from typing import Dict

from .graph_model import Node, Edge


class GraphView(tk.Canvas):
    """Tkinter Canvas-based view for rendering a workflow graph.

    The implementation is intentionally minimal; it focuses on rendering
    nodes and edges so that more advanced interaction can be added later.
    """

    def __init__(self, master=None, **kwargs):
        background = kwargs.pop("background", "#222")
        super().__init__(master, background=background, **kwargs)
        self.node_items: Dict[str, int] = {}
        self.edge_items: Dict[str, int] = {}
        self.port_radius = 4

    # -- Rendering ---------------------------------------------------------------
    def add_node(self, node: Node) -> None:
        """Render a node on the canvas."""
        x = node.ui.get("x", 0)
        y = node.ui.get("y", 0)
        width = node.ui.get("width", 120)
        height = node.ui.get("height", 40)
        rect = self.create_rectangle(
            x, y, x + width, y + height,
            fill="#444", outline="#888",
            tags=("node", node.id)
        )
        self.create_text(
            x + width / 2,
            y + height / 2,
            text=node.label,
            fill="white",
            tags=("label", node.id)
        )
        self.node_items[node.id] = rect
        # Ports
        for idx, port in enumerate(node.ports_out):
            px = x + width
            py = y + 10 + idx * 12
            self._draw_port(px, py, node.id, port.id, "out")
        for idx, port in enumerate(node.ports_in):
            px = x
            py = y + 10 + idx * 12
            self._draw_port(px, py, node.id, port.id, "in")

    def _draw_port(self, x: int, y: int, node_id: str, port_id: str, direction: str) -> None:
        r = self.port_radius
        self.create_oval(
            x - r, y - r, x + r, y + r,
            fill="white", outline="black",
            tags=("port", f"{node_id}:{port_id}", direction)
        )

    def connect(self, edge: Edge) -> None:
        """Render an edge connecting two existing nodes."""
        src_item = self.find_withtag(f"{edge.src[0]}:{edge.src[1]}")
        dst_item = self.find_withtag(f"{edge.dst[0]}:{edge.dst[1]}")
        if not src_item or not dst_item:
            return
        sx, sy, _, _ = self.bbox(src_item[0])
        dx, dy, _, _ = self.bbox(dst_item[0])
        sx += self.port_radius
        sy += self.port_radius
        dx += self.port_radius
        dy += self.port_radius
        line = self.create_line(sx, sy, dx, dy, arrow=tk.LAST, fill="white", tags=("edge", edge.id))
        self.edge_items[edge.id] = line

    def layout(self, strategy: str = "manual") -> None:
        """Placeholder for future layout algorithms."""
        # Currently nodes are positioned manually using the coordinates stored
        # in ``Node.ui``. Layout strategies can be added without changing the
        # public API.
        return
