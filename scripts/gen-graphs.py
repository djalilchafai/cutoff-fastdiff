#!/usr/bin/env python3
"""Generate docs/dependencies.md: the statement dependency graph and the module import graph.

The statement graph is read from the compiled proofs, not written by hand: for each advertised
theorem `T` (comparator.json), the proof of its development lemma `T'` is traversed through the
project's own declarations, and an edge `T -> S` is recorded when it reaches another advertised
lemma `S'`. Mathlib is not traversed. The graph is then transitively reduced for readability.

Run `lake build` first, then `python3 scripts/gen-graphs.py`.
"""
import json
import pathlib
import re
import subprocess
import sys
import tempfile

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "docs" / "dependencies.md"

LEAN_QUERY = r"""
import Cutfast
open Lean

def inProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `Cutfast
  | none => false

def body? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- The advertised lemmas reached from the proof of `root`, not traversing other advertised
lemmas nor declarations outside the project. -/
def reach (env : Environment) (nodes : NameSet) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let c := stack.back
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if c != root && nodes.contains c then
      out := out.insert c
      continue
    if c != root && !inProject env c then continue
    if let some ci := env.find? c then
      let cs := ci.type.getUsedConstants ++ ((body? ci).map (·.getUsedConstants) |>.getD #[])
      for d in cs do
        unless seen.contains d do stack := stack.push d
  return out

#eval show CoreM Unit from do
  let env ← getEnv
  let names : List Name := [NAMES]
  let nodes := names.foldl (·.insert ·) ({} : NameSet)
  for n in names do
    IO.println s!"EDGES {n} {(reach env nodes n).toList}"
"""

DISTANCE = {"wassersteinSq": "W₂²", "relEntropy": "Hₘ", "fisherInfo": "Iₘ"}

# (class, legend title, membership test on the paper source, fill, stroke)
GROUPS = [
    ("pde", "Sections 1.2–1.4.2", lambda s: s.startswith(("Section 1.2", "Section 1.3",
                                                          "Section 1.4.2")), "#f0efec", "#8a8985"),
    ("cutoff", "Theorems 1.1, 1.2 and Section 1.4.3",
     lambda s: s.startswith(("Theorem", "Section 1.4.3")), "#cde2fb", "#2a78d6"),
    ("wass", "Lemmas 2.1, 2.2", lambda s: s.startswith("Lemma 2"), "#d3f0e3", "#1baf7a"),
    ("moments", "Lemmas 3.1, 4.1, 4.2",
     lambda s: s.startswith(("Lemma 3", "Lemma 4", "After Lemma 4")), "#fbe0d3", "#eb6834"),
    ("remarks", "Remarks 3.2, 4.3", lambda s: s.startswith("Remark"), "#e6e2f8", "#6250d6"),
]


def short(name: str) -> str:
    return name.removeprefix("Cutfast.").rstrip("'")


def statement_edges(names: list[str]) -> dict[str, set[str]]:
    lean_names = ", ".join(f"`{n}'" for n in names)
    with tempfile.TemporaryDirectory() as tmp:
        query = pathlib.Path(tmp) / "Deps.lean"
        query.write_text(LEAN_QUERY.replace("NAMES", lean_names), encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(query)], cwd=ROOT,
                                capture_output=True, text=True)
    if result.returncode != 0:
        sys.exit(f"lean query failed:\n{result.stdout}\n{result.stderr}")
    edges = {}
    for line in result.stdout.splitlines():
        m = re.fullmatch(r"EDGES (\S+) \[(.*)\]", line)
        if m:
            targets = [t.strip() for t in m.group(2).split(",") if t.strip()]
            edges[short(m.group(1))] = {short(t) for t in targets}
    if set(edges) != {short(n) for n in names}:
        sys.exit("lean query output is incomplete")
    return edges


def transitive_reduction(edges: dict[str, set[str]]) -> dict[str, set[str]]:
    def reachable(start: str) -> set[str]:
        seen, stack = set(), list(edges[start])
        while stack:
            node = stack.pop()
            if node not in seen:
                seen.add(node)
                stack.extend(edges[node])
        return seen
    return {a: {b for b in bs if not any(b in reachable(c) for c in bs - {b})}
            for a, bs in edges.items()}


def node_of(name: str, source: str) -> tuple[str, str]:
    """Node id and label. The three distances of a cutoff statement share one node."""
    if any(k in name for k in DISTANCE) and source.startswith(("Theorem", "Section 1.4.3")):
        base = name
        for k in DISTANCE:
            base = base.replace(k, "X")
        theorem = "Theorem 1.2" if "fixedExponent" in name else "Theorem 1.1"
        head = theorem if source.startswith("Theorem") else f"Section 1.4.3 ({theorem})"
        lean = base.replace("X", "{wassersteinSq, relEntropy, fisherInfo}")
        return base, f"{head}<br/>W₂², Hₘ, Iₘ<br/><code>{lean}</code>"
    head = re.sub(r"W₂ infinite for d ≤ 2", "W₂² = ∞ for heavy tails", source)
    return name, f"{head}<br/><code>{name}</code>"


def statement_graph(names: list[str], sources: dict[str, str]) -> str:
    edges = statement_edges(names)
    ids, labels, groups = {}, {}, {}
    for n in map(short, names):
        node, text = node_of(n, sources[n])
        ids[n] = node
        labels[node] = text
        group = next((g[0] for g in GROUPS if g[2](sources[n])), None)
        if group is None:
            sys.exit(f"statement without a group: {n}")
        groups[node] = group
    merged: dict[str, set[str]] = {node: set() for node in labels}
    for a, bs in edges.items():
        merged[ids[a]] |= {ids[b] for b in bs if ids[b] != ids[a]}
    merged = transitive_reduction(merged)
    used = {b for bs in merged.values() for b in bs}
    isolated = [node for node in labels if not merged[node] and node not in used]
    lines = ["```mermaid", "flowchart LR"]
    for key, _, _, fill, stroke in GROUPS:
        lines.append(f"  classDef {key} fill:{fill},stroke:{stroke},color:#0b0b0b")
    for node, text in labels.items():
        if node in isolated:
            continue
        lines.append(f'  {node}["{text}"]:::{groups[node]}')
    for a in labels:
        for b in sorted(merged[a]):
            lines.append(f"  {a} --> {b}")
    lines.append("```")
    legend = " · ".join(f"{title} ({fill_name})" for (_, title, _, _, _), fill_name in
                        zip(GROUPS, ["gray", "blue", "green", "orange", "violet"]))
    alone = ", ".join(f"`{node}`" for node in isolated)
    return ("\n".join(lines) + f"\n\nColors: {legend}.\n\n"
            f"Not drawn: {len(isolated)} statements whose proofs use no other advertised statement "
            f"and are used by none: {alone}.")


def module_graph() -> str:
    lines = ["```mermaid", "flowchart TB"]
    modules = sorted(p.stem for p in (ROOT / "Cutfast").glob("*.lean"))
    imports = {}
    for m in modules:
        text = (ROOT / "Cutfast" / f"{m}.lean").read_text(encoding="utf-8")
        imports[m] = {i for i in re.findall(r"^(?:public )?import Cutfast\.(\w+)", text, re.M)}
    reduced = transitive_reduction(imports)
    for m in modules:
        lines.append(f"  {m}[{m}]")
    for m in modules:
        for i in sorted(reduced[m]):
            lines.append(f"  {m} --> {i}")
    lines.append("```")
    return "\n".join(lines)


def main() -> None:
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    names = config["theorem_names"]
    alignment = yaml.safe_load((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    sources = {short(s["lean"]): s["source"] for s in alignment["alignment"]["statements"]}
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(f"""# Dependency graphs

Generated by `scripts/gen-graphs.py` from the compiled proofs; do not edit by hand.

## Which results each proof uses

An arrow `A → B` means that the Lean proof of `A` uses the statement `B`, directly or through
intermediate lemmas of the development (Mathlib is not followed). Arrows implied by others are
omitted. A statement without outgoing arrows is proved from Mathlib and the development's own
lemmas only. See `FORMALIZATION_GUIDE.md` for each statement.

{statement_graph(names, sources)}

## Module imports

`A → B` means that `Cutfast/A.lean` imports `Cutfast/B.lean` (imports implied by others are
omitted). `Defs` holds the definitions of `Challenge.lean`.

{module_graph()}
""", encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
