"""A small JSON Schema validator, Python standard library only, for the subset these schemas use.

Used by check_docs.py when the `jsonschema` module is not installed (or when MREG_DOCS_NO_JSONSCHEMA=1). Supported:
type (name or list), enum, const, required, properties, additionalProperties (bool or schema), propertyNames (pattern),
items, prefixItems, minItems, maxItems, uniqueItems, minLength, maxLength, minimum, maximum, pattern, anyOf, oneOf, allOf,
$ref to a JSON pointer inside the same document ("#/..."). Everything else (title, description, $comment, default,
x-* keywords, format) is ignored.
"""
import re


def _type_ok(v, t):
    if t == "object":
        return isinstance(v, dict)
    if t == "array":
        return isinstance(v, list)
    if t == "string":
        return isinstance(v, str)
    if t == "boolean":
        return isinstance(v, bool)
    if t == "null":
        return v is None
    if t == "integer":
        return isinstance(v, int) and not isinstance(v, bool)
    if t == "number":
        return isinstance(v, (int, float)) and not isinstance(v, bool)
    raise ValueError(f"unknown type {t!r}")


def resolve(root, ref):
    if not ref.startswith("#"):
        raise ValueError(f"only local references are supported: {ref}")
    node = root
    for part in [p for p in ref[1:].split("/") if p]:
        part = part.replace("~1", "/").replace("~0", "~")
        node = node[part]
    return node


def validate(instance, schema, root=None, path=""):
    """List of (path, message) errors; empty when the instance is valid."""
    root = schema if root is None else root
    errs = []
    if "$ref" in schema:
        try:
            errs += validate(instance, resolve(root, schema["$ref"]), root, path)
        except (KeyError, ValueError) as e:
            errs.append((path, f"unresolvable $ref {schema['$ref']}: {e}"))
    if "type" in schema:
        ts = schema["type"] if isinstance(schema["type"], list) else [schema["type"]]
        if not any(_type_ok(instance, t) for t in ts):
            return errs + [(path, f"{instance!r:.60} is not of type {ts}")]
    if "const" in schema and not (instance == schema["const"] and type(instance) is type(schema["const"])):
        errs.append((path, f"{instance!r:.60} is not {schema['const']!r}"))
    if "enum" in schema and not any(instance == e and type(instance) is type(e) for e in schema["enum"]):
        errs.append((path, f"{instance!r:.60} is not one of {schema['enum']}"))
    if isinstance(instance, str):
        if "minLength" in schema and len(instance) < schema["minLength"]:
            errs.append((path, "string too short"))
        if "maxLength" in schema and len(instance) > schema["maxLength"]:
            errs.append((path, "string too long"))
        if "pattern" in schema and not re.search(schema["pattern"], instance):
            errs.append((path, f"{instance!r:.60} does not match {schema['pattern']!r}"))
    if isinstance(instance, (int, float)) and not isinstance(instance, bool):
        if "minimum" in schema and instance < schema["minimum"]:
            errs.append((path, f"{instance} is below {schema['minimum']}"))
        if "maximum" in schema and instance > schema["maximum"]:
            errs.append((path, f"{instance} is above {schema['maximum']}"))
    if isinstance(instance, dict):
        for k in schema.get("required", []):
            if k not in instance:
                errs.append((path, f"{k!r} is a required property"))
        props = schema.get("properties", {})
        for k, sub in props.items():
            if k in instance:
                errs += validate(instance[k], sub, root, f"{path}/{k}")
        if "propertyNames" in schema:
            for k in instance:
                errs += [(f"{path}/{k}", "property name: " + m) for _, m in validate(k, schema["propertyNames"], root, "")]
        ap = schema.get("additionalProperties", True)
        for k in instance:
            if k in props:
                continue
            if ap is False:
                errs.append((f"{path}/{k}", "additional property not allowed"))
            elif isinstance(ap, dict):
                errs += validate(instance[k], ap, root, f"{path}/{k}")
    if isinstance(instance, list):
        if "minItems" in schema and len(instance) < schema["minItems"]:
            errs.append((path, "too few items"))
        if "maxItems" in schema and len(instance) > schema["maxItems"]:
            errs.append((path, "too many items"))
        if schema.get("uniqueItems") and len({repr(x) for x in instance}) != len(instance):
            errs.append((path, "items are not unique"))
        pre = schema.get("prefixItems", [])
        for i, sub in enumerate(pre):
            if i < len(instance):
                errs += validate(instance[i], sub, root, f"{path}/{i}")
        if "items" in schema:
            for i, x in enumerate(instance[len(pre):], start=len(pre)):
                errs += validate(x, schema["items"], root, f"{path}/{i}")
    if "allOf" in schema:
        for sub in schema["allOf"]:
            errs += validate(instance, sub, root, path)
    if "anyOf" in schema and not any(not validate(instance, sub, root, path) for sub in schema["anyOf"]):
        errs.append((path, "matches none of the anyOf alternatives"))
    if "oneOf" in schema:
        n = sum(1 for sub in schema["oneOf"] if not validate(instance, sub, root, path))
        if n != 1:
            errs.append((path, f"matches {n} of the oneOf alternatives, not exactly one"))
    return errs


def refs_of(node):
    """All $ref strings in a schema document."""
    if isinstance(node, dict):
        for k, v in node.items():
            if k == "$ref" and isinstance(v, str):
                yield v
            else:
                yield from refs_of(v)
    elif isinstance(node, list):
        for v in node:
            yield from refs_of(v)
