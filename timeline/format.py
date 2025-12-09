"""timeline.format

Provide compact timeline serialization. Try to use msgpack when available,
fall back to gzipped JSON when not.
"""
import json
import gzip
import time
from typing import Any

try:
    import msgpack
except Exception:
    msgpack = None


def save_timeline(obj: Any, path: str):
    """Save timeline object to `path`. If extension endswith .mpk use msgpack,
    if endswith .gz use gzipped JSON, otherwise JSON.
    """
    if path.endswith('.mpk') and msgpack is not None:
        with open(path, 'wb') as f:
            packed = msgpack.packb(obj, use_bin_type=True)
            f.write(packed)
    elif path.endswith('.gz'):
        with gzip.open(path, 'wt', encoding='utf-8') as f:
            json.dump(obj, f)
    else:
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(obj, f, indent=2)


def load_timeline(path: str):
    """Load timeline created by `save_timeline`.
    Returns the deserialized object.
    """
    if path.endswith('.mpk') and msgpack is not None:
        with open(path, 'rb') as f:
            return msgpack.unpackb(f.read(), raw=False)
    elif path.endswith('.gz'):
        with gzip.open(path, 'rt', encoding='utf-8') as f:
            return json.load(f)
    else:
        with open(path, 'r', encoding='utf-8') as f:
            return json.load(f)
