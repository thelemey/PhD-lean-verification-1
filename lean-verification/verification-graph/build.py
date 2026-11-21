#!/usr/bin/env python3
"""Build the dependency atlas of the corrected dissertation and its Lean coverage."""

from collections import Counter, defaultdict
from functools import cache
from graphlib import TopologicalSorter
from html import escape
import json
from pathlib import Path
import re
import subprocess
from textwrap import wrap

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent
TEX = LEAN.parent / "corrected_thesis" / "thesis_corrected.tex"
TEX_LINK = "../../corrected_thesis/thesis_corrected.tex"
CLAIM_FILL = "#FFEB80"

# Each entry gives the text label, border colour and meaning of a status.
STATUSES = {
    "verified": ("Доказано", "#228044", "Указанные теоремы Lean покрывают формулировку."),
    "definition": ("Определено", "#629740", "В Lean задан объект, используемый в доказательстве."),
    "qualified": ("С уточнением", "#A68812", "Условия или существенный шаг доказательства в Lean уточнены в таблице."),
    "partial": ("Частично", "#D3791A", "Проверена часть утверждения или частный случай."),
    "unmarked": ("Без проверки Lean", "#C43735", "В проекте для этого утверждения отсутствует указанное доказательство."),
}
TOPICS = {
    "words": ("Свойства слов и конкатенация факториалов", ("2.1", "2.2")),
    "fibonacci": ("Слова, плотности и ряды Фибоначчи", ("3.1", "3.2", "3.3", "3.4", "3.5")),
    "palindromes": ("Палиндромные префиксы и богатство", ("3.6",)),
    "dynamics": ("Метрика, скрученные повторы и динамика", ("3.7", "3.8")),
    "applications": ("Разрезы полимино и анализ эксперимента", ("4.2", "4.3")),
    "trees": ("Индексы графов и двумерная рекурсия", ("5.1", "5.2", "5.3", "5.4")),
}
KINDS = {
    "theorem": "Теорема", "lemma": "Лемма", "proposition": "Предложение",
    "proposition*": "Предложение", "corollary": "Следствие", "observation": "Наблюдение",
    "definition": "Определение", "problem": "Задача", "hypothesize": "Гипотеза",
    "conjecture": "Гипотеза", "convention": "Соглашение",
}


def tex_index(lines):
    """Track the chapter, section and theorem counters declared in the preamble."""
    chapter = section = 0
    global_counts = Counter()
    current = None
    sections, statements, expected = {}, {}, set()
    env = re.compile(r"\\(begin|end)\{(" + "|".join(map(re.escape, KINDS)) + r")\}")
    for number, line in enumerate(lines, 1):
        if re.match(r"\s*\\chapter\{", line):
            chapter += 1
            section = 0
        if re.match(r"\s*\\section\{", line):
            section += 1
            counts = Counter()
        sections[number] = f"{chapter}.{section}"
        for action, kind in env.findall(line):
            if action == "end":
                if current:
                    statements.update(dict.fromkeys(range(current[0], number + 1), current))
                current = None
                continue
            counter = kind if kind in {"definition", "lemma", "conjecture"} else "theorem"
            caption = KINDS[kind]
            if kind == "conjecture":
                global_counts[counter] += 1
                caption += f" {global_counts[counter]}"
            elif not kind.endswith("*"):
                counts[counter] += 1
                caption += f" {chapter}.{section}.{counts[counter]}"
            current = (number, caption)
            if kind != "definition":
                expected.add(number)
    return sections, statements, expected


def anchor(key):
    return "node-" + re.sub(r"[^a-z0-9-]", "-", key.lower())


@cache
def module_text(module):
    return (LEAN / "Thesis" / f"{module}.lean").read_text()


def lean_links(key, evidence):
    links = []
    for module, names in evidence.items():
        source = module_text(module)
        for name in names:
            pattern = (
                r"^(?:@\[[^\n]+\]\s*)?(?:(?:noncomputable|protected) )*"
                r"(?:theorem|lemma|def|abbrev) " + re.escape(name) + r"(?=[\s:{(])"
            )
            matches = list(re.finditer(pattern, source, re.M))
            if len(matches) != 1:
                raise ValueError(f"{key}: expected one declaration of {module}.{name}")
            line = source.count("\n", 0, matches[0].start()) + 1
            links.append(f"[{name}](../Thesis/{module}.lean#L{line})")
    return links


def load_nodes():
    graph = json.loads((HERE / "graph.json").read_text())
    marks = json.loads((HERE / "status.json").read_text())
    lines = [re.sub(r"(?<!\\)%.*", "", line) for line in TEX.read_text().splitlines()]
    sections, statements, expected = tex_index(lines)
    if graph.keys() != marks.keys() or len({anchor(k) for k in graph}) != len(graph):
        raise ValueError("Graph, statuses or Markdown anchors disagree")
    assigned = set()
    for key, node in graph.items():
        needle = node.get("at", rf"\label{{{key}}}")
        found = [n for n, line in enumerate(lines, 1) if needle in line]
        if len(found) != 1:
            raise ValueError(f"{key}: expected a unique TeX anchor, found {found}")
        line = found[0]
        caption = node.get("kind")
        if not caption:
            if line not in statements:
                raise ValueError(f"{key}: missing TeX statement or explicit caption")
            start, caption = statements[line]
            if "part" in node:
                part = node["part"]
                if rf"\item[({part})]" not in lines[line - 1]:
                    raise ValueError(f"{key}: part {part} not found on line {line}")
                caption += f" ({part})"
            else:
                line = start
                if line in assigned:
                    raise ValueError(f"Duplicate TeX statement on line {line}")
                assigned.add(line)
        node.update(line=line, caption=caption, section=sections[line], **marks[key])
        node["links"] = lean_links(key, node.get("lean", {}))
        st = node["status"]
        if st not in STATUSES or bool(node["links"]) != (st != "unmarked"):
            raise ValueError(f"{key}: inconsistent status and Lean evidence")
        if st in {"partial", "qualified"} and not node.get("note"):
            raise ValueError(f"{key}: coverage needs an explanation")
        needs = node.get("uses", [])
        if len(needs) != len(set(needs)) or set(needs) - graph.keys():
            raise ValueError(f"{key}: invalid dependency list {needs}")
    if expected - assigned:
        raise ValueError(f"Missing TeX statements on lines {sorted(expected - assigned)}")
    tuple(TopologicalSorter({k: n.get("uses", []) for k, n in graph.items()}).static_order())
    if {n["section"] for n in graph.values()} != {s for _, ss in TOPICS.values() for s in ss}:
        raise ValueError("TeX sections and thematic views disagree")
    return dict(sorted(graph.items(), key=lambda pair: pair[1]["line"]))


def tags(node):
    return [f"{name} {node[field]}" for field, name in
            (("novelty", "Новизна"), ("defense", "Защита")) if field in node]


def dot_string(text):
    return json.dumps(text, ensure_ascii=False)


def make_dot(nodes, keys, title, coverage, *, direction, pack=False):
    legend = "".join(
        f'<TD BORDER="3" COLOR="{color}" CELLPADDING="5">{label}</TD>'
        for label, color, _ in STATUSES.values()
    )
    heading = (
        '<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="6">'
        f'<TR><TD COLSPAN="5"><FONT POINT-SIZE="19"><B>{escape(title)}</B></FONT></TD></TR>'
        '<TR><TD COLSPAN="5">Исправленная диссертация · стрелка ведёт от предпосылки к результату</TD></TR>'
        f'<TR>{legend}</TR>'
        f'<TR><TD COLSPAN="5" BGCOLOR="{CLAIM_FILL}" CELLPADDING="4">'
        'Жёлтый фон — научная новизна или положение, вынесенное на защиту</TD></TR></TABLE>'
    )
    layout = f"rankdir={direction}, " + ('pack=true, packmode="array3", ' if pack else "")
    dot = [
        "digraph corrected_thesis {",
        f'graph [label=<{heading}>, labelloc=t, bgcolor="white", pad=0.28, '
        f'{layout}nodesep=0.24, ranksep=0.46, fontname="DejaVu Sans", fontsize=10];',
        'node [shape=box, style="rounded,filled", fillcolor="white", penwidth=3, '
        'margin="0.12,0.08", fontname="DejaVu Sans", fontsize=11, fontcolor="#202A32"];',
        'edge [color="#72818B", arrowsize=0.65];',
    ]
    by_section = defaultdict(list)
    for key in keys:
        by_section[nodes[key]["section"]].append(key)
    for section, members in by_section.items():
        dot += [f'subgraph "cluster_{section}" {{',
                f'graph [label="§ {section}", labeljust=l, style="rounded", color="#C8D0D5", margin=14];']
        for key in members:
            node = nodes[key]
            status, color, _ = STATUSES[node["status"]]
            title_lines = wrap(node["title"], 32, break_long_words=False, break_on_hyphens=False)
            claim_tags = tags(node)
            subtitle = " · ".join([node["caption"], *claim_tags])
            fill = f'fillcolor="{CLAIM_FILL}", ' if claim_tags else ""
            label = (f'<FONT POINT-SIZE="9">{escape(subtitle)}</FONT><BR/><B>'
                     + "<BR/>".join(map(escape, title_lines))
                     + f'</B><BR/><FONT POINT-SIZE="9">{status}</FONT>')
            tip = f"{node['caption']}. {node['title']}. {status}. " + node.get("note", "")
            dot.append(f'{dot_string(key)} [id="{anchor(key)}", label=<{label}>, color="{color}", '
                       f'{fill}URL="{coverage}#{anchor(key)}", tooltip={dot_string(tip)}];')
        dot.append("}")
    selected = set(keys)
    for target in keys:
        for source in nodes[target].get("uses", []):
            if source in selected:
                dot.append(f"{dot_string(source)} -> {dot_string(target)};")
    dot.append("}")
    return "\n".join(dot) + "\n"


def node_link(key, nodes):
    return f"[{nodes[key]['title']}](#{anchor(key)})"


def introduction_items(title):
    lines = TEX.read_text().splitlines()
    heading = rf"\section*{{{title}}}"
    start, = (i for i, line in enumerate(lines) if heading in line)
    items = []
    for i in range(start + 1, len(lines)):
        line = lines[i].strip()
        if line == r"\end{enumerate}":
            return items
        if line.startswith(r"\item "):
            items.append(i + 1)
    raise ValueError(f"Missing list in TeX section: {title}")


def report(nodes):
    counts = Counter(n["status"] for n in nodes.values())
    highlighted = Counter(n["status"] for n in nodes.values() if tags(n))
    edges = sum(len(n.get("uses", [])) for n in nodes.values())
    out = ["# Граф зависимостей исправленной диссертации", "",
           f"В графе {len(nodes)} узлов и {edges} непосредственных зависимостей. "
           "Стрелка ведёт от предпосылки к утверждению, которое на неё опирается. "
           "В карту входят все теоремы, леммы, предложения, следствия и наблюдения TeX, "
           "используемые определения, отдельные шаги доказательств и выводы эксперимента. "
           "Жёлтым фоном выделены утверждения из разделов введения «Научная новизна работы» и "
           "«Положения, выносимые на защиту». Цвет рамки показывает статус проверки в Lean. "
           "Если доказательству достаточно частного случая "
           "более общей предпосылки, это указано в таблице. Номера новизны и защиты следуют введению. "
           f"[Исправленный TeX]({TEX_LINK}) · [Полный граф (SVG)](verification_graph.svg)", "",
           "## Цвет рамки", "",
           "| Статус | Цвет | Всего узлов | Из них жёлтых | Что проверено |", "|---|---|---:|---:|---|"]
    colors = ("Зелёный", "Светло-зелёный", "Золотистый", "Оранжевый", "Красный")
    for (key, (name, color, meaning)), shade in zip(STATUSES.items(), colors):
        out.append(f"| {name} | {shade} `{color}` | {counts[key]} | {highlighted[key]} | {meaning} |")
    out += ["", "## Разделы", "", "Каждая схема раздела также показывает его непосредственные предпосылки из других разделов.", ""]
    for slug, (name, sections) in TOPICS.items():
        out.append(f"- § {', '.join(sections)}. [{name}](sections/{slug}.svg)")
    out += ["", "## Положения введения", "", "| Пункт введения | Утверждения на графе |", "|---|---|"]
    for field, name, heading in (("defense", "Защита", "Положения, выносимые на защиту"),
                                 ("novelty", "Новизна", "Научная новизна работы")):
        items = introduction_items(heading)
        if {n[field] for n in nodes.values() if field in n} != set(range(1, len(items) + 1)):
            raise ValueError(f"Graph and TeX disagree on {field} items")
        for i, line in enumerate(items, 1):
            refs = [node_link(k, nodes) for k, n in nodes.items() if n.get(field) == i]
            out.append(f"| [{name} {i}]({TEX_LINK}#L{line}) | {' · '.join(refs)} |")
    for _, (name, sections) in TOPICS.items():
        out += ["", f"## {name}", "", "| Утверждение в исправленном TeX | Статус Lean | Непосредственные предпосылки | Проверка в Lean |", "|---|---|---|---|"]
        for key, node in nodes.items():
            if node["section"] not in sections:
                continue
            src = f"[§ {node['section']} · {node['caption']}]({TEX_LINK}#L{node['line']})"
            label = f'<a name="{anchor(key)}"></a> **{node["title"]}**'
            badge = " · ".join(tags(node))
            inputs = " · ".join(node_link(k, nodes) for k in node.get("uses", []))
            details = " ".join(filter(None, (node.get("note"), ", ".join(node["links"]))))
            cells = [f"{label}<br>{src}" + (f"<br>{badge}" if badge else ""),
                     STATUSES[node["status"]][0], inputs or "—", details or "—"]
            out.append("| " + " | ".join(c.replace("|", "&#124;") for c in cells) + " |")
    return "\n".join(out) + "\n"


def render(dot, output):
    subprocess.run(["dot", "-Tsvg", "-o", str(output)], input=dot, text=True, check=True)


def main():
    nodes = load_nodes()
    full = make_dot(nodes, list(nodes), "Зависимости утверждений и проверка в Lean",
                    "coverage.md", direction="LR", pack=True)
    (HERE / "verification_graph.dot").write_text(full)
    render(full, HERE / "verification_graph.svg")
    folder = HERE / "sections"
    folder.mkdir(exist_ok=True)
    for slug, (title, sections) in TOPICS.items():
        inside = {k for k, n in nodes.items() if n["section"] in sections}
        inputs = {k for n in inside for k in nodes[n].get("uses", [])}
        selected = [k for k in nodes if k in inside or k in inputs]
        direction = "TB" if slug in {"dynamics", "applications"} else "LR"
        render(make_dot(nodes, selected, title, "../coverage.md", direction=direction),
               folder / f"{slug}.svg")
    (HERE / "coverage.md").write_text(report(nodes))


if __name__ == "__main__":
    main()
