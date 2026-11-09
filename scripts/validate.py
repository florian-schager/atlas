"""Validate all entries in data/ against the JSON schemas and check cross-references.

Usage: python scripts/validate.py
Exits with status 1 if any problem is found.
"""
import json
import re
import sys
from pathlib import Path

import yaml
from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parent.parent
KINDS = {"authors": "author", "venues": "venue", "papers": "paper", "results": "result",
         "reductions": "reduction"}


def load_entries():
    entries, errors = {}, []
    for folder, kind in KINDS.items():
        schema = json.loads((ROOT / "schema" / f"{kind}.schema.json").read_text(encoding="utf-8"))
        validator = Draft202012Validator(schema, format_checker=Draft202012Validator.FORMAT_CHECKER)
        entries[folder] = {}
        for path in sorted((ROOT / "data" / folder).glob("*.yaml")):
            rel = path.relative_to(ROOT).as_posix()
            obj = yaml.safe_load(path.read_text(encoding="utf-8"))
            for err in validator.iter_errors(obj):
                loc = "/".join(str(p) for p in err.absolute_path) or "(root)"
                errors.append(f"{rel}: {loc}: {err.message}")
            if not isinstance(obj, dict):
                continue
            if obj.get("id") != path.stem:
                errors.append(f"{rel}: id '{obj.get('id')}' does not match file name")
            entries[folder][path.stem] = obj
    return entries, errors


def check_references(entries):
    errors = []
    authors, venues, papers = entries["authors"], entries["venues"], entries["papers"]
    for pid, paper in papers.items():
        for a in paper.get("authors", []):
            if a not in authors:
                errors.append(f"papers/{pid}: unknown author '{a}'")
        for v in paper.get("versions", []):
            if v.get("venue") not in venues:
                errors.append(f"papers/{pid}: unknown venue '{v.get('venue')}'")
            elif venues[v["venue"]]["type"] != v.get("type"):
                errors.append(f"papers/{pid}: version type '{v.get('type')}' does not match venue '{v['venue']}'")
    for rid, result in entries["results"].items():
        if result.get("problem") in ("vertex-coloring", "edge-coloring") and "colors" not in result:
            errors.append(f"results/{rid}: coloring results need 'colors'")
        target = entries["results"].get(result.get("reduce_to"))
        if result.get("reduce_to") and target is None:
            errors.append(f"results/{rid}: reduce_to: unknown result '{result['reduce_to']}'")
        elif target is not None:
            # An algorithm comes from a reduction from its problem to the target's; a lower bound travels the
            # other way: a lower bound for the target's problem gives one for every problem it reduces to.
            lower = result.get("bound") == "lower"
            if lower and target.get("bound") != "lower":
                errors.append(f"results/{rid}: a lower bound can only be derived from a lower bound")
            if not lower and target.get("bound") == "lower":
                errors.append(f"results/{rid}: an algorithm cannot be derived from a lower bound")
            src, dst = (target.get("problem"), result.get("problem")) if lower else (result.get("problem"), target.get("problem"))
            fits = [x for x in entries["reductions"].values()
                    if (x["from"]["problem"], x["to"]["problem"]) == (src, dst)
                    and x.get("graph_class", result.get("graph_class")) == result.get("graph_class")]
            if result.get("via"):
                named = entries["reductions"].get(result["via"])
                if named is None:
                    errors.append(f"results/{rid}: via: unknown reduction '{result['via']}'")
                fits = [x for x in fits if x is named]
            if not fits:
                errors.append(f"results/{rid}: no reduction from {src} to {dst} for {result.get('graph_class')}")
            elif not any(result.get("model") in x["models"] for x in fits):
                errors.append(f"results/{rid}: no reduction from {src} to {dst} in {result.get('model')}")
            elif (not lower and result.get("randomness") == "deterministic"
                  and all(x.get("randomness") == "randomized" for x in fits if result.get("model") in x["models"])):
                errors.append(f"results/{rid}: deterministic, but the reduction from {src} to {dst} is randomized")
            # Algorithms carry over from CONGEST to LOCAL, lower bounds from LOCAL to CONGEST, not back.
            weaker, stronger = ("LOCAL", "CONGEST") if lower else ("CONGEST", "LOCAL")
            if result.get("model") == weaker and target.get("model") == stronger:
                errors.append(f"results/{rid}: {weaker}, but the result it comes from only holds in {stronger}")
            if result.get("year", 0) < target.get("year", 0):
                errors.append(f"results/{rid}: year {result.get('year')} is before the result it reduces to ({target['year']})")
        if result.get("problem") == "network-decomposition" and "decomposition" not in result:
            errors.append(f"results/{rid}: network decomposition results need 'decomposition'")
        splitting = result.get("problem") == "degree-splitting"
        for key in ("discrepancy", "variant"):
            if splitting and key not in result:
                errors.append(f"results/{rid}: degree splitting results need '{key}'")
            if not splitting and key in result:
                errors.append(f"results/{rid}: '{key}' is only for degree splitting results")
    for folder in ("results", "reductions"):
        for rid, entry in entries[folder].items():
            for s in entry.get("sources", []):
                if s.get("paper") not in papers:
                    errors.append(f"{folder}/{rid}: unknown paper '{s.get('paper')}'")
            for ref in re.findall(r"\[\[([^\]]*)\]\]", entry.get("comments", "")):
                if ref not in papers and ref not in entries["results"]:
                    errors.append(f"{folder}/{rid}: comment links unknown result or paper '{ref}'")
            earliest = [min(v["year"] for v in papers[s["paper"]]["versions"])
                        for s in entry.get("sources", []) if s.get("paper") in papers]
            if earliest and entry.get("year") is not None and entry["year"] < min(earliest):
                errors.append(f"{folder}/{rid}: year {entry['year']} is before all of its sources ({min(earliest)})")
            if entry.get("sources") and entry.get("year") is None:
                errors.append(f"{folder}/{rid}: entries with sources need a year")
    used_authors = {a for p in papers.values() for a in p.get("authors", [])}
    used_venues = {v["venue"] for p in papers.values() for v in p.get("versions", [])}
    used_papers = {s["paper"] for folder in ("results", "reductions")
                   for r in entries[folder].values() for s in r.get("sources", [])}
    for kind, ids, used in (("authors", authors, used_authors), ("venues", venues, used_venues),
                            ("papers", papers, used_papers)):
        for unused in sorted(set(ids) - used):
            print(f"note: {kind}/{unused} is not referenced")
    return errors


def main():
    entries, errors = load_entries()
    errors += check_references(entries)
    counts = ", ".join(f"{len(v)} {k}" for k, v in entries.items())
    if errors:
        print("\n".join(errors))
        print(f"{len(errors)} problem(s) in {counts}")
        sys.exit(1)
    print(f"OK: {counts}")


if __name__ == "__main__":
    main()
