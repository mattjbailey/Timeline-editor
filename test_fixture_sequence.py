import json
from types import SimpleNamespace

from lighting_designer.fixture_sequence import (
    FixtureLook,
    FixtureSequence,
    SequenceMarker,
    interpolate_value,
    evaluate_look,
    map_values_by_type,
)
from lighting_designer.models import LightingProject


def test_sequence_round_trip_preserves_markers_and_speed():
    sequence = FixtureSequence(
        name="Mover Sweep",
        group_id="group-1",
        group_name="Front Movers",
        duration=8.0,
        speed_multiplier=2.0,
        markers=[
            SequenceMarker(
                time=3.0,
                name="Color change",
                looks=[FixtureLook("fixture-1", {"pan": 180, "gobo": 4})],
            ),
            SequenceMarker(
                time=0.0,
                name="Start",
                looks=[FixtureLook("fixture-1", {"pan": 10, "gobo": 0})],
            ),
        ],
    )

    restored = FixtureSequence.from_dict(json.loads(json.dumps(sequence.to_dict())))

    assert restored.name == "Mover Sweep"
    assert restored.speed_multiplier == 2.0
    assert [marker.name for marker in restored.sorted_markers()] == ["Start", "Color change"]
    assert restored.effective_duration() == 4.0


def test_interpolation_supports_smooth_and_step_values():
    assert interpolate_value(0, 100, 0.25) == 25.0
    assert interpolate_value(0, 100, 0.25, "step") == 0
    assert interpolate_value(0, 100, 1.0, "step") == 100
    assert interpolate_value("red", "blue", 0.5) == "red"


def test_distribution_uses_stage_x_and_supports_reverse_and_alternating():
    fixtures = [
        SimpleNamespace(id="right", stage_x=20),
        SimpleNamespace(id="left", stage_x=-20),
        SimpleNamespace(id="middle", stage_x=0),
    ]

    sequence = FixtureSequence(distribution="left_to_right", stagger_seconds=0.25)
    assert sequence.ordered_fixture_ids(fixtures) == ["left", "middle", "right"]
    assert sequence.fixture_start_offset(2, 3) == 0.5

    sequence.distribution = "right_to_left"
    assert sequence.ordered_fixture_ids(fixtures) == ["right", "middle", "left"]

    sequence.distribution = "alternating"
    assert sequence.ordered_fixture_ids(fixtures) == ["left", "right", "middle"]


def test_finite_loop_stops_at_sequence_end():
    sequence = FixtureSequence(duration=4.0, speed_multiplier=1.0, loop=True, loop_count=2)
    assert sequence.marker_time(7.0) == 3.0
    assert sequence.marker_time(8.0) == 4.0


def test_authored_marker_uses_profile_defaults_without_live_output():
    fixture = SimpleNamespace(
        id="fixture-1",
        mode=SimpleNamespace(channels=[
            SimpleNamespace(type="pan", default=12),
            SimpleNamespace(type="gobo", default=4),
        ]),
    )

    marker = SequenceMarker.authored(1.5, "Down", fixture)

    assert marker.time == 1.5
    assert marker.looks[0].values == {"0:pan": 12, "1:gobo": 4}


def test_project_round_trip_preserves_fixture_sequences():
    sequence = FixtureSequence(name="Project Sequence", group_id="group-1")
    project = LightingProject(name="Test Project", fixture_sequences=[sequence])

    restored = LightingProject.from_dict(project.to_dict())

    assert len(restored.fixture_sequences) == 1
    assert restored.fixture_sequences[0].id == sequence.id
    assert restored.fixture_sequences[0].group_id == "group-1"


def test_evaluate_look_interpolates_between_markers():
    sequence = FixtureSequence(
        duration=4.0,
        markers=[
            SequenceMarker(time=0.0, looks=[FixtureLook("src", {"0:tilt": 0})]),
            SequenceMarker(time=4.0, looks=[FixtureLook("src", {"0:tilt": 200})]),
        ],
    )
    assert evaluate_look(sequence, 0.0) == {"0:tilt": 0}
    assert evaluate_look(sequence, 2.0)["0:tilt"] == 100.0
    assert evaluate_look(sequence, 4.0) == {"0:tilt": 200}


def test_map_values_by_type_drives_targets_by_channel_type():
    source_values = {"0:tilt": 180, "1:dimmer": 255}
    target_types = ["dimmer", "tilt", "pan"]

    mapped = map_values_by_type(source_values, target_types)

    assert mapped == {0: 255, 1: 180}


def test_wave_offset_produces_staggered_phase_across_group():
    sequence = FixtureSequence(
        duration=4.0,
        distribution="left_to_right",
        stagger_seconds=1.0,
        markers=[
            SequenceMarker(time=0.0, looks=[FixtureLook("src", {"0:tilt": 0})]),
            SequenceMarker(time=4.0, looks=[FixtureLook("src", {"0:tilt": 200})]),
        ],
    )
    elapsed = 2.0
    first = sequence.marker_time(elapsed - sequence.fixture_start_offset(0, 3))
    second = sequence.marker_time(elapsed - sequence.fixture_start_offset(1, 3))

    assert evaluate_look(sequence, first)["0:tilt"] == 100.0
    assert evaluate_look(sequence, second)["0:tilt"] == 50.0

