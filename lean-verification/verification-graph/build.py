#!/usr/bin/env python3
"""Overlay Lean coverage on the dissertation's existing dependency graph."""

from html import escape
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent
SOURCE = LEAN.parent / "dependency_graph_bundle"
STATUSES = {
    "verified": "Доказано",
    "qualified": "С уточнением",
    "partial": "Частично",
    "definition": "Определение",
    "unmarked": "Без отметки",
}
STATUS_COLORS = {
    "verified": "#065F46",
    "qualified": "#613C88",
    "partial": "#85480C",
    "definition": "#174C7B",
    "unmarked": "#4A5563",
}
NODE_LINE = re.compile(
    r'^"(?P<id>[^"]+)" \[label="(?P<label>(?:[^"\\]|\\.)*)", '
    r'.* id="node-(?P=id)"[^]]*\];$', re.MULTILINE
)


def dot_text(value):
    return json.dumps(value, ensure_ascii=False)[1:-1]


def lean_links(entry):
    links = []
    for module, declarations in entry.get("lean", {}).items():
        path = LEAN / "Thesis" / f"{module}.lean"
        text = path.read_text(encoding="utf-8")
        for declaration in declarations:
            name = re.escape(declaration)
            match = re.search(
                rf"^(?:@\[[^\n]+\] )?(?:(?:noncomputable|protected) )?"
                rf"(?:theorem|lemma|def|abbrev) {name}(?=[\s:{{(])",
                text,
                re.MULTILINE,
            )
            if not match:
                raise ValueError(f"{path}: declaration {declaration} not found")
            line = text.count("\n", 0, match.start()) + 1
            links.append(f"[`{declaration}`](../Thesis/{module}.lean#L{line})")
    return ", ".join(links)


def coverage_markdown(graph, entries):
    lines = [
        "# Узлы графа и доказательства Lean",
        "",
        "Метки в квадратных скобках, цвета и стрелки взяты из графа экспертизы "
        "представленной редакции. Статус Lean относится к указанным теоремам и "
        "их формулировкам в исправленном TeX.",
        "",
        "- **Доказано** — утверждение узла покрыто указанными теоремами.",
        "- **С уточнением** — доказана исправленная формулировка либо формулировка "
        "с указанным условием.",
        "- **Частично** — в узле есть проверенный результат и непокрытая часть.",
        "- **Определение** — в Lean задан объект, используемый в доказательстве.",
        "- **Без отметки** — для узла в этой карте не указано доказательство Lean.",
        "",
        "Полный перечень работ, включая утверждения за пределами исходного графа, "
        "приведён в [VERIFICATION.md](../VERIFICATION.md).",
    ]
    for group, title in graph["groups"].items():
        lines += [
            "", f"## {title}", "",
            "| Узел | Статус Lean | Покрытие и ссылки |",
            "|---|---|---|",
        ]
        for node in graph["nodes"]:
            if node["group"] != group:
                continue
            key = node["id"]
            entry = entries[key]
            status = STATUSES[entry["status"]]
            details = " ".join(part for part in (entry.get("note"), lean_links(entry)) if part) or "—"
            caption = f'<a name="node-{key.lower()}"></a> **{key}** {node["title"]}'
            lines.append(f"| {caption} | {status} | {details.replace('|', '&#124;')} |")
    return "\n".join(lines) + "\n"


def main():
    graph = json.loads((SOURCE / "dependency_graph.json").read_text(encoding="utf-8"))
    original = (SOURCE / "dependency_graph.dot").read_text(encoding="utf-8")
    marks = json.loads((HERE / "status.json").read_text(encoding="utf-8"))
    ids = {node["id"] for node in graph["nodes"]}
    if set(marks) - ids:
        raise ValueError(f"Unknown graph nodes: {sorted(set(marks) - ids)}")
    if {match["id"] for match in NODE_LINE.finditer(original)} != ids:
        raise ValueError("Original DOT and JSON disagree on node IDs")
    entries = {key: marks.get(key, {"status": "unmarked"}) for key in ids}

    def annotate(match):
        key = match["id"]
        entry = entries[key]
        status = STATUSES[entry["status"]]
        link = f'URL="coverage.md#node-{key.lower()}"'
        line = match[0]
        start = match.start("label") - match.start() - 1
        end = match.end("label") - match.start() + 1
        original_label = json.loads(line[start:end])
        body = "<BR/>".join(escape(part) for part in original_label.splitlines())
        color = STATUS_COLORS[entry["status"]]
        badge = f'<FONT COLOR="{color}"><B>Lean: {escape(status)}</B></FONT>'
        line = f"{line[:start]}<{body}<BR/>{badge}>{line[end:]}"
        summary = " ".join(part for part in (f"Lean: {status}.", entry.get("note")) if part)
        line = line.replace('tooltip="', f'tooltip="{dot_text(summary)} | ', 1)
        return f"{line[:-2]}, {link}];"

    dot = NODE_LINE.sub(annotate, original).replace('bgcolor="transparent"', 'bgcolor="white"', 1)
    legend = (
        "Граф верификации диссертации в Lean\n"
        "Сохранены узлы и стрелки графа зависимостей\n"
        "Цвета и метки в квадратных скобках — экспертная оценка исходной редакции\n"
        "Строка Lean — доказано · с уточнением · частично · определение · без отметки"
    )
    dot = dot.replace("graph [", f'graph [label="{dot_text(legend)}", labelloc=t, ', 1)
    report = coverage_markdown(graph, entries)
    dot_path = HERE / "verification_graph.dot"
    dot_path.write_text(dot, encoding="utf-8")
    subprocess.run(["dot", "-Tsvg", dot_path.name, "-o", "verification_graph.svg"], cwd=HERE, check=True)
    (HERE / "coverage.md").write_text(report, encoding="utf-8")


if __name__ == "__main__":
    main()
