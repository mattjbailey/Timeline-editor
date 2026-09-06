"""Reusable, group-targeted fixture sequence data and evaluation helpers."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
import uuid
from typing import Any, Iterable


@dataclass
class FixtureLook:
    """Authored parameter values for one fixture at a sequence marker."""

    fixture_id: str
    values: dict[str, Any] = field(default_factory=dict)
    channel_types: dict[str, str] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "FixtureLook":
        return cls(
            fixture_id=str(data.get("fixture_id", "")),
            values=dict(data.get("values", {}) or {}),
            channel_types=dict(data.get("channel_types", {}) or {}),
        )


@dataclass
class SequenceMarker:
    """Authored fixture parameters at a position on the sequence timeline."""

    time: float
    name: str = "Marker"
    looks: list[FixtureLook] = field(default_factory=list)
    interpolation: dict[str, str] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "time": float(self.time),
            "name": self.name,
            "looks": [look.to_dict() for look in self.looks],
            "interpolation": dict(self.interpolation),
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "SequenceMarker":
        return cls(
            time=max(0.0, float(data.get("time", 0.0))),
            name=str(data.get("name", "Marker")),
            looks=[FixtureLook.from_dict(item) for item in data.get("looks", [])],
            interpolation=dict(data.get("interpolation", {}) or {}),
        )

    @classmethod
    def authored(cls, time: float, name: str, fixture: Any) -> "SequenceMarker":
        """Create a marker from profile defaults, never from live DMX state."""
        values = {}
        channel_types = {}
        for index, channel in enumerate(getattr(fixture.mode, "channels", []) or []):
            key = f"{index}:{channel.type}"
            values[key] = int(getattr(channel, "default", 0))
            channel_types[key] = channel.type
        return cls(
            time=max(0.0, float(time)),
            name=name or "Marker",
            looks=[FixtureLook(str(fixture.id), values, channel_types)],
        )


@dataclass
class FixtureSequence:
    """Named reusable sequence that normally targets one project group."""

    id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = "New Sequence"
    target_type: str = "group"
    group_id: str = ""
    group_name: str = ""
    source_fixture_id: str = ""
    source_fixture_name: str = ""
    duration: float = 4.0
    speed_multiplier: float = 1.0
    loop: bool = True
    loop_count: int = 0
    distribution: str = "simultaneous"
    stagger_seconds: float = 0.0
    intensity_only_distribution: bool = True
    markers: list[SequenceMarker] = field(default_factory=list)
    version: int = 1

    def to_dict(self) -> dict[str, Any]:
        return {
            "version": self.version,
            "id": self.id,
            "name": self.name,
            "target_type": self.target_type,
            "group_id": self.group_id,
            "group_name": self.group_name,
            "source_fixture_id": self.source_fixture_id,
            "source_fixture_name": self.source_fixture_name,
            "duration": max(0.0, float(self.duration)),
            "speed_multiplier": max(0.01, float(self.speed_multiplier)),
            "loop": bool(self.loop),
            "loop_count": max(0, int(self.loop_count)),
            "distribution": self.distribution,
            "stagger_seconds": max(0.0, float(self.stagger_seconds)),
            "intensity_only_distribution": bool(self.intensity_only_distribution),
            "markers": [marker.to_dict() for marker in self.sorted_markers()],
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "FixtureSequence":
        return cls(
            id=str(data.get("id", str(uuid.uuid4()))),
            name=str(data.get("name", "New Sequence")),
            target_type=str(data.get("target_type", "group")),
            group_id=str(data.get("group_id", "")),
            group_name=str(data.get("group_name", "")),
            source_fixture_id=str(data.get("source_fixture_id", "")),
            source_fixture_name=str(data.get("source_fixture_name", "")),
            duration=max(0.0, float(data.get("duration", 4.0))),
            speed_multiplier=max(0.01, float(data.get("speed_multiplier", 1.0))),
            loop=bool(data.get("loop", True)),
            loop_count=max(0, int(data.get("loop_count", 0))),
            distribution=str(data.get("distribution", "simultaneous")),
            stagger_seconds=max(0.0, float(data.get("stagger_seconds", 0.0))),
            intensity_only_distribution=bool(
                data.get("intensity_only_distribution", True)
            ),
            markers=[
                SequenceMarker.from_dict(marker)
                for marker in data.get("markers", [])
            ],
            version=int(data.get("version", 1)),
        )

    def sorted_markers(self) -> list[SequenceMarker]:
        return sorted(self.markers, key=lambda marker: marker.time)

    def effective_duration(self) -> float:
        return max(0.0, self.duration) / max(0.01, self.speed_multiplier)

    def marker_time(self, elapsed: float) -> float:
        """Return local sequence time after speed and loop handling."""
        duration = self.effective_duration()
        if duration <= 0.0:
            return 0.0
        if elapsed < 0.0:
            return 0.0
        if not self.loop:
            return min(elapsed * self.speed_multiplier, duration)
        if self.loop_count > 0 and elapsed >= duration * self.loop_count:
            return duration
        return (elapsed * self.speed_multiplier) % duration

    def ordered_fixture_ids(self, fixtures: Iterable[Any]) -> list[str]:
        """Order current group members for visual distribution modes."""
        members = list(fixtures)
        members.sort(key=lambda fixture: (
            float(getattr(fixture, "location_x", getattr(fixture, "stage_x", getattr(fixture, "x", 0.0)))),
            str(getattr(fixture, "id", "")),
        ))
        if self.distribution == "right_to_left":
            members.reverse()
        if self.distribution == "alternating":
            members = members[::2] + members[1::2]
        return [str(getattr(fixture, "id", fixture)) for fixture in members]

    def fixture_start_offset(self, index: int, fixture_count: int) -> float:
        if self.distribution == "simultaneous" or fixture_count <= 1:
            return 0.0
        if self.distribution in {"left_to_right", "right_to_left", "alternating"}:
            return max(0.0, self.stagger_seconds) * index
        return 0.0


def interpolate_value(first: Any, second: Any, amount: float, mode: str = "smooth") -> Any:
    """Interpolate numeric values, or use the second value for step values."""
    if mode == "step" or not isinstance(first, (int, float)) or not isinstance(second, (int, float)):
        return first if amount < 1.0 else second
    return first + (second - first) * max(0.0, min(1.0, amount))


def _first_look_values(marker: SequenceMarker) -> dict[str, Any]:
    """Authored parameter values for a marker's source look (first look)."""
    return dict(marker.looks[0].values) if marker.looks else {}


def evaluate_look(sequence: FixtureSequence, local_time: float) -> dict[str, Any]:
    """Interpolate the authored source look at a local sequence time.

    Returns a mapping of "index:type" keys to values, blending between the
    two surrounding markers per each parameter's interpolation mode.
    """
    markers = sequence.sorted_markers()
    if not markers:
        return {}
    if local_time <= markers[0].time:
        return _first_look_values(markers[0])
    if local_time >= markers[-1].time:
        return _first_look_values(markers[-1])
    for index in range(len(markers) - 1):
        left, right = markers[index], markers[index + 1]
        if left.time <= local_time <= right.time:
            span = right.time - left.time
            amount = 0.0 if span <= 0.0 else (local_time - left.time) / span
            left_values = _first_look_values(left)
            right_values = _first_look_values(right)
            result: dict[str, Any] = {}
            for key, start_value in left_values.items():
                mode = right.interpolation.get(key, left.interpolation.get(key, "smooth"))
                result[key] = interpolate_value(
                    start_value, right_values.get(key, start_value), amount, mode
                )
            return result
    return _first_look_values(markers[-1])


def map_values_by_type(
    source_values: dict[str, Any], target_channel_types: list[str]
) -> dict[int, int]:
    """Map interpolated source values onto target channel indices by type.

    Source keys are "index:type"; target channels are matched by channel type
    in order, so a template authored on one fixture drives every group member.
    """
    from collections import defaultdict

    by_type: dict[str, list[Any]] = defaultdict(list)
    for key in sorted(source_values, key=lambda item: int(item.split(":", 1)[0])):
        _, _, channel_type = key.partition(":")
        by_type[channel_type].append(source_values[key])

    result: dict[int, int] = {}
    cursor: dict[str, int] = defaultdict(int)
    for target_index, channel_type in enumerate(target_channel_types):
        values = by_type.get(channel_type)
        if not values:
            continue
        pick = min(cursor[channel_type], len(values) - 1)
        result[target_index] = int(round(float(values[pick])))
        cursor[channel_type] += 1
    return result
