from __future__ import annotations

from dataclasses import dataclass, field, asdict
from typing import Dict, List, Tuple, Any, Optional
import json
import uuid


@dataclass
class Port:
    """Represents a typed connection point on a node."""

    id: str
    type: str = "flow"
    required: bool = False


@dataclass
class Node:
    """A single step in the workflow graph."""

    id: str
    type: str
    label: str
    ports_in: List[Port] = field(default_factory=list)
    ports_out: List[Port] = field(default_factory=list)
    meta: Dict[str, Any] = field(default_factory=dict)
    ui: Dict[str, Any] = field(default_factory=dict)  # x, y, etc.


@dataclass
class Edge:
    """A directed connection between two node ports."""

    id: str
    src: Tuple[str, str]  # (node_id, port_id)
    dst: Tuple[str, str]
    label: Optional[str] = None
    meta: Dict[str, Any] = field(default_factory=dict)


@dataclass
class GraphModel:
    """In-memory representation of the node graph."""

    nodes: Dict[str, Node] = field(default_factory=dict)
    edges: Dict[str, Edge] = field(default_factory=dict)
    version: str = "1.0"

    # -- Node and Edge management -------------------------------------------------
    def add_node(self, node: Node) -> None:
        if node.id in self.nodes:
            raise ValueError(f"Node {node.id} already exists")
        self.nodes[node.id] = node

    def remove_node(self, node_id: str) -> None:
        self.nodes.pop(node_id, None)
        # Remove edges touching this node
        self.edges = {
            eid: e for eid, e in self.edges.items()
            if e.src[0] != node_id and e.dst[0] != node_id
        }

    def connect(self, edge: Edge) -> None:
        if edge.id in self.edges:
            raise ValueError(f"Edge {edge.id} already exists")
        if edge.src[0] not in self.nodes or edge.dst[0] not in self.nodes:
            raise ValueError("Edge references unknown node")
        self.edges[edge.id] = edge

    def disconnect(self, edge_id: str) -> None:
        self.edges.pop(edge_id, None)

    # -- Serialization ------------------------------------------------------------
    def to_dict(self) -> Dict[str, Any]:
        return {
            "version": self.version,
            "nodes": {nid: asdict(n) for nid, n in self.nodes.items()},
            "edges": {eid: asdict(e) for eid, e in self.edges.items()},
        }

    def to_json(self) -> str:
        """Serialize the graph to a JSON string."""
        return json.dumps(self.to_dict(), indent=2)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "GraphModel":
        version = data.get("version", "1.0")
        nodes = {
            nid: Node(
                id=node["id"],
                type=node.get("type", "node"),
                label=node.get("label", nid),
                ports_in=[Port(**p) for p in node.get("ports_in", [])],
                ports_out=[Port(**p) for p in node.get("ports_out", [])],
                meta=node.get("meta", {}),
                ui=node.get("ui", {}),
            )
            for nid, node in data.get("nodes", {}).items()
        }
        edges = {
            eid: Edge(
                id=edge["id"],
                src=tuple(edge["src"]),
                dst=tuple(edge["dst"]),
                label=edge.get("label"),
                meta=edge.get("meta", {}),
            )
            for eid, edge in data.get("edges", {}).items()
        }
        return cls(nodes=nodes, edges=edges, version=version)

    @classmethod
    def from_json(cls, data: str) -> "GraphModel":
        return cls.from_dict(json.loads(data))

    # -- Validation ---------------------------------------------------------------
    def validate(self) -> List[str]:
        """Return a list of human-readable validation errors."""
        errors: List[str] = []

        # Validate edge endpoints
        for edge in self.edges.values():
            src_node = self.nodes.get(edge.src[0])
            dst_node = self.nodes.get(edge.dst[0])
            if not src_node or not dst_node:
                errors.append(f"Edge {edge.id} references missing node")
                continue
            if edge.src[1] not in {p.id for p in src_node.ports_out}:
                errors.append(f"Edge {edge.id} invalid source port")
            if edge.dst[1] not in {p.id for p in dst_node.ports_in}:
                errors.append(f"Edge {edge.id} invalid destination port")

        # Ensure required inputs have incoming edges
        for node in self.nodes.values():
            required_inputs = {p.id for p in node.ports_in if p.required}
            connected_inputs = {
                e.dst[1] for e in self.edges.values() if e.dst[0] == node.id
            }
            missing = required_inputs - connected_inputs
            if missing:
                errors.append(
                    f"Node {node.id} missing inputs: {', '.join(sorted(missing))}"
                )

        return errors


# Utility -----------------------------------------------------------------------
def new_id() -> str:
    """Return a random hexadecimal identifier."""
    return uuid.uuid4().hex
