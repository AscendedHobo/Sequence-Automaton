import json

from automation_maker2.graph_model import GraphModel, Node, Edge, Port


def build_sample_graph() -> GraphModel:
    model = GraphModel()
    start = Node(id="start", type="start", label="Start", ports_out=[Port(id="out")], ui={"x": 0, "y": 0})
    end = Node(id="end", type="end", label="End", ports_in=[Port(id="in", required=True)], ui={"x": 100, "y": 0})
    model.add_node(start)
    model.add_node(end)
    model.connect(Edge(id="e1", src=("start", "out"), dst=("end", "in")))
    return model


def test_round_trip_serialization():
    model = build_sample_graph()
    data = model.to_json()
    loaded = GraphModel.from_json(data)
    assert loaded.nodes["start"].label == "Start"
    assert loaded.edges["e1"].src == ("start", "out")


def test_validate_missing_input():
    model = GraphModel()
    task = Node(id="n1", type="task", label="Task", ports_in=[Port(id="p1", required=True)])
    model.add_node(task)
    errors = model.validate()
    assert errors, "Expected validation error for missing required input"
