from __future__ import annotations

from pathlib import Path
from typing import Optional, Tuple

from .graph_model import GraphModel, Node, Edge, Port, new_id
from .graph_view import GraphView


class GraphController:
    """Controller that coordinates a :class:`GraphModel` with a :class:`GraphView`.

    This class is intentionally lightweight; it wires together the model and
    view layers and provides convenience methods for creating nodes and edges
    programmatically. User interactions (dragging, context menus, etc.) can be
    added on top of this controller without changing its API.
    """

    def __init__(self, view: GraphView, model: Optional[GraphModel] = None) -> None:
        self.view = view
        self.model = model or GraphModel()

    # -- Node & Edge creation ----------------------------------------------------
    def create_node(
        self,
        type: str,
        label: str,
        ports_in: Optional[list[Port]] = None,
        ports_out: Optional[list[Port]] = None,
        **ui,
    ) -> Node:
        node = Node(
            id=new_id(),
            type=type,
            label=label,
            ports_in=ports_in or [],
            ports_out=ports_out or [],
            ui=ui,
        )
        self.model.add_node(node)
        self.view.add_node(node)
        return node

    def connect(
        self,
        src: Tuple[str, str],
        dst: Tuple[str, str],
        label: Optional[str] = None,
    ) -> Edge:
        edge = Edge(id=new_id(), src=src, dst=dst, label=label)
        self.model.connect(edge)
        self.view.connect(edge)
        return edge

    # -- Persistence -------------------------------------------------------------
    def save(self, path: str | Path) -> None:
        Path(path).write_text(self.model.to_json(), encoding="utf-8")

    def load(self, path: str | Path) -> None:
        data = Path(path).read_text(encoding="utf-8")
        self.model = GraphModel.from_json(data)
        # Rebuild canvas
        self.view.delete("all")
        for node in self.model.nodes.values():
            self.view.add_node(node)
        for edge in self.model.edges.values():
            self.view.connect(edge)
