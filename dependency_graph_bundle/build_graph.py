#!/usr/bin/env python3
"""Build an audited dependency map, SVG, PDF atlas, and reproducible bundle."""
from pathlib import Path
import json
import subprocess
import textwrap
import zipfile
from xml.sax.saxutils import escape
import xml.etree.ElementTree as ET

import fitz
from reportlab.pdfgen import canvas
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.pagesizes import A4, A3, A1, landscape
from reportlab.lib.colors import HexColor
from reportlab.platypus import Paragraph
from reportlab.lib.styles import ParagraphStyle

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parent.parent / "tmp" / "dependencies"
WORK.mkdir(parents=True, exist_ok=True)
PALETTE = {
    "ok":       ("#E7F2E9", "#338153", "0", "В проверенном фрагменте ошибок не выявлено"),
    "local":    ("#FFF3C4", "#B78300", "1", "Локальная поправка; итоговый вывод сохраняется"),
    "gap":      ("#FFE3AC", "#C47700", "2", "Обоснование / объект требует восстановления"),
    "false":    ("#FFD5BD", "#CC5200", "3", "Существенно неверная формула или утверждение"),
    "critical": ("#FBC9D0", "#B51F37", "4", "Противоречие в определении объекта"),
    "novelty":  ("#E9DDF6", "#8054A6", "Н", "Замечание к новизне или статусу, не к истинности"),
    "external": ("#EEF1F5", "#748193", "И", "Внешний факт или отдельное рассуждение рецензента"),
}
NODES = []
EDGES = []

def node(id, group, title, body, status="ok", note="", source="", issue=None):
    NODES.append(dict(id=id, group=group, title=title, body=body, status=status,
                      note=note, source=source, issue=issue))

def edge(a, b, why, kind="proof"):
    EDGES.append(dict(source=a, target=b, why=why, kind=kind))

GROUPS = {
    "factorials": "2.2  Конкатенация факториалов",
    "prelim": "3.1  Ошибки предварительного раздела",
    "fibonacci": "3.4–3.5  Буквы, механическое описание, обрамления",
    "palindromes": "3.6  Палиндромы",
    "twisted": "3.8  Скрученные повторы и динамика",
    "trees": "5.1  Деревья и индексы",
    "metrics": "3.7–3.8  Метрика",
    "polyomino": "4.2  Разрезание полимино",
}

node("E1", "factorials", "Текст перед леммой 2.2.1", "«log(n!) не равномерно\nраспределён mod 1»", "false",
     "Утверждение неверно. Для любого фиксированного b>1 дробные части log_b(n!) равномерно распределены. В доказательстве леммы 2.2.1 это отрицательное утверждение не используется.",
     "с. 43; строка 924 TeX", "E1")
node("F1", "factorials", "Лемма 2.2.1", "Бесконечно много попаданий\nв каждый интервал mod 1",
     source="с. 43–44")
node("F2", "factorials", "Лемма 2.2.2", "Заданный ненулевой префикс\nв записи n!", source="с. 44")
node("F3", "factorials", "Лемма 2.2.3", "Произвольно длинный\nконцевой блок нулей", source="с. 44")
node("F4", "factorials", "Предл. 2.2.2", "p(k) ≤ a(k) ≤ b^k", source="с. 45")
node("F5", "factorials", "Теорема 2.2.3", "Полная факторная и\nарифметическая сложность", source="с. 45–46")
edge("F1", "F2", "Дробные части логарифма определяют ведущие цифры.")
edge("F2", "F5", "Ненулевой хвост заданного фактора помещается в начало (n+1)!.")
edge("F3", "F5", "Начальные нули фактора берутся из конца предыдущего факториала.")
edge("F4", "F5", "Часть (ii) следует из части (i) и p≤a≤b^k.")

node("E2", "prelim", "Формула (3.4)", "Вторая сумма равна F(n+1),\nа не F(n)", "local",
     "При F0=0, F1=1 две напечатанные суммы дают при n=3 значения 2 и 3. Это локальная ошибка индексации. В показанных доказательствах используется отдельная рекурсия / формула Бине.",
     "с. 49; формула (3.4)", "E2")
node("E3", "prelim", "Определение 3.1.2", "При k=3, p=1:\nF₁¹(t,3)=0 и F₁¹(t,3)=1", "critical",
     "Начальные условия (3.8) противоречат друг другу. Объект в напечатанном определении не существует для этих разрешённых параметров. Уровень 4 относится к этому определению, а не ко всей диссертации.",
     "с. 49; формулы (3.7), (3.8)", "E3")
node("A1", "prelim", "Лемма 3.1.1", "Производящая функция (3.11)\nдля объекта из опр. 3.1.2", "gap",
     "Формула относится к последовательности из противоречивого определения. До исправления определения утверждение нельзя принимать в текущей форме. Это не самостоятельное доказательство ложности формулы после восстановления правильных условий.",
     "с. 50; формула (3.11)", "E3a")
edge("E3", "A1", "Определение задаёт объект леммы; требуется восстановление.", "object")
node("E4", "prelim", "Теорема 3.1.1", "(3.13): 2·limsup[…] вместо\n2 + limsup[…] при смысле E*", "false",
     "ind и ind* не определены. Если ind* означает асимптотический критический показатель, множитель 2 ошибочен: нужен 2+limsup. Для Фибоначчи получаются 2φ и 2+φ соответственно. Эту формулу последующие показанные доказательства не используют.",
     "с. 50–51; формула (3.13)", "E4")

node("B0", "fibonacci", "Рекурсия слова Фибоначчи", "s₀=0, s₁=01;\nsₙ=sₙ₋₁sₙ₋₂", "external",
     "Фиксированное исходное определение классического слова, использованное в разных частях текста.")
node("B1", "fibonacci", "Предл. 3.4.1", "Механическое представление\nбукв слова Фибоначчи", source="с. 57")
node("B2", "fibonacci", "Теорема 3.4.2", "Точный подсчёт букв\nи оптимальное отклонение", source="с. 57–58")
node("B3", "fibonacci", "Предл. 3.4.3", "Сбалансированность\nвсех факторов", source="с. 59–60")
node("B4", "fibonacci", "Леммы 3.5.1 → 3.5.2", "Позиции Битти;\nзапрет факторов 11 и 000", source="с. 66–67")
node("B5", "fibonacci", "Предл. 3.5.3 → 3.5.4", "Количество букв\nв uₘ и qₘ=a uₘ b", source="с. 69")
node("B6", "fibonacci", "Лемма 3.1.2", "Тождества Бине\nи предельные отношения", source="с. 52")
node("B7", "fibonacci", "Теорема 3.5.5", "Точная погрешность плотности\nв обрамлённых словах", source="с. 70")
edge("B1", "B2", "Телескопическая сумма механических букв.")
edge("B1", "B3", "Разность целых частей для произвольного окна.")
edge("B1", "B4", "Лемма 3.5.1 выводится из механического описания; из неё следует 3.5.2.")
edge("B0", "B5", "Количества букв удовлетворяют рекурсии Фибоначчи; обрамление добавляет по одной букве.")
edge("B5", "B7", "Исходная точная дробь для плотности.")
edge("B6", "B7", "Тождество Бине даёт остаток и его знак.")

node("C1", "palindromes", "Лемма 3.6.1", "Явные палиндромные\nпрефиксы Фибоначчи", source="с. 74–75")
node("C2", "palindromes", "Теорема 3.6.2 (Фишлер)", "densₚ(w) ≤ 1/φ\nдля непериодического w", source="с. 74")
node("C3", "palindromes", "Теорема 3.6.3", "densₚ(f)=1/φ", source="с. 75")
node("C4", "palindromes", "Лемма 3.6.2", "y = ι₀(ρ(f))\n[1: вложенность лишь с n=1]", "local",
     "Обнаружена дополнительная граничная неточность: y₀=01 не является префиксом y₁=02. Утверждение о вложенности верно для n≥1. Предельное кодирование y=ι₀(ρ(f)) сохраняется; в доказательстве богатства y₀ нужно рассмотреть отдельно или использовать, что s₋₁=1 является фактором f.",
     "с. 77–78; лемма 3.6.2", "E6")
node("C5", "palindromes", "Лемма 3.6.3", "Длины палиндромных\nпрефиксов: m → 2m+1", source="с. 78")
node("C6", "palindromes", "Предл. 3.6.7", "Вставка нуля\nсохраняет densₚ", source="с. 78–79")
node("C7", "palindromes", "Теорема 3.6.8", "Префиксы y: 2Fₖ−3;\ndensₚ(y)=1/φ", source="с. 79")
node("C8", "palindromes", "Лемма 3.6.4", "Подсчёт палиндромов\nпри вставке разделителя", source="с. 79–80")
node("C9", "palindromes", "Теорема 3.6.10", "Богатство yₙ\nи всех факторов y", source="с. 80")
node("C10", "palindromes", "Теоремы 3.6.12 → 3.6.13", "Список префиксов;\nформула Фишлера через CF", source="с. 81")
node("C11", "palindromes", "Предл. 3.6.14; след. 3.6.15", "Дихотомия плотности\nи её следствия", source="с. 81–83")
node("C12", "palindromes", "Классические факты", "Все палиндромные префиксы f;\nбогатство штурмовых факторов", "external",
     "Полнота списка префиксов берётся из классической литературы, а не из одной леммы 3.6.1.")
edge("B0", "C1", "Индукция по рекурсии конечных слов.")
edge("C1", "C3", "Даёт верхнюю оценку limsup отношений длин.")
edge("C2", "C3", "Даёт противоположную оценку.")
edge("B0", "C4", "Сравнение рекурсий и переименование букв.")
edge("C5", "C6", "Аффинная замена длин сохраняет limsup отношений.")
edge("C4", "C7", "Структура бесконечного слова y.")
edge("C5", "C7", "Преобразование полного списка длин.")
edge("C12", "C7", "Полный список палиндромных префиксов f.")
edge("C4", "C9", "Представление yₙ через слова Фибоначчи.")
edge("C8", "C9", "Удвоение числа палиндромов в слове с разделителями.")
edge("C12", "C9", "Богатство исходных штурмовых факторов.")
edge("C10", "C11", "Анализ ограниченности неполных частных; для остальных пунктов используются также внешние классические факты.")
edge("C2", "C11", "Верхняя оценка 1/φ в пункте (1) следствия.")

node("D0", "twisted", "Предл. 3.8.1 / 3.8.4", "W[n]=s_b(n) mod N", source="с. 90–91, 93")
node("D1", "twisted", "Лемма 3.8.4", "Повторы ↔ постоянство cₘ;\nарифметика переносов", source="с. 93–94")
node("D2", "twisted", "Леммы 3.8.1–3.8.3", "Двоичный случай:\nредукция длины блока", source="с. 91–92")
node("D3", "twisted", "Теорема 3.8.2", "Классификация\nскрученных кубов при b=2", source="с. 92")
node("E5", "twisted", "Теорема 3.8.5", "Полная классификация κ\n[1: поправка в доказательстве]", "local",
     "В конце шага 2 при j'≥b неверно написано floor(2b/j')≤1; нужно ≤2. Значение κ=max{2,floor(2b/j')} и вывод теоремы сохраняются.",
     "с. 94–95; последняя строка доказательства", "E5")
node("D4", "twisted", "Следствие 3.8.6", "Непериодичность;\nчастные случаи классификации", source="с. 95–96")
node("D5", "twisted", "Теорема 3.8.7 (1,2,4,5)", "Примитивность, минимальность,\nчастоты, строгая эргодичность", source="с. 96–97")
node("D6", "twisted", "Теорема 3.8.7 (3)", "Непериодичность,\nлинейная сложность, h=0", source="с. 96–97")
node("D7", "twisted", "Следствие 3.8.8", "Запрет повторов\nна всём подсдвиге X_W", source="с. 97")
node("N1", "twisted", "Наблюдение 3.8.3", "Точная закономерность p(n)\nоставлена открытым вопросом", "novelty",
     "Полная факторная сложность s₂(n) mod N вычислена Tromp–Shallit (1995). Требуется сопоставление с известной формулой; вычислительное наблюдение само по себе не объявляется ложным.",
     "с. 93, 98, 134", "N1")
node("D8", "twisted", "Внешние классические факты", "Примитивные подстановки;\nтеорема Морса–Хедлунда", "external")
node("D9", "twisted", "Tromp–Shallit, 1995", "Факторная сложность\ns₂(n) mod N", "external")
edge("D0", "D1", "Повторы выражаются через разности сумм цифр.")
edge("D0", "D2", "Двоичное арифметическое представление.")
edge("D2", "D3", "Редукция к нечётной длине и противоречие для m≥3.")
edge("D1", "E5", "Ограничение и построение постоянных окон cₘ.")
edge("E5", "D4", "Конечность κ исключает финальную периодичность.")
edge("D0", "D5", "Блочная структура и примитивность подстановки.")
edge("D8", "D5", "Стандартная теорема о примитивных подстановках.")
edge("D4", "D6", "Непериодичность.")
edge("D0", "D6", "Независимая блочная оценка p(k)<N²bk.")
edge("D8", "D6", "Нижняя оценка Морса–Хедлунда.")
edge("E5", "D7", "Граница отсутствующих повторов.")
edge("D5", "D7", "Минимальность даёт совпадение языков.")
edge("D9", "N1", "Сопоставить с известной полной функцией.", "context")

node("G0", "trees", "Штурмов язык", "p(k)=k+1;\nправый специальный фактор rₖ", "external")
node("G1", "trees", "Предл. 5.1.1", "Нижняя оценка\nirr₂(T) ≥ Δ(Δ²−1)", source="с. 126")
node("G2", "trees", "Предл. 5.1.2", "Путь минимизирует irr₂", source="с. 126")
node("G3", "trees", "Теорема 5.1.3", "Индексы дерева факторов\nштурмова слова", source="с. 128–129")
node("N2", "trees", "Гипотеза 1", "Звезда максимизирует irr₂\n[Н: уже есть простое доказательство]", "novelty",
     "Утверждение истинно: каждое ребро даёт не более Δ²−1, а для незвезды Δ≤n−2. Требуется заменить гипотезу предложением. Это замечание к статусу, не контрпример.",
     "с. 126–127, заключение", "N2")
node("G4", "trees", "Рассуждение рецензента", "Незвезда: Δ≤n−2;\n|d(u)²−d(v)²|≤Δ²−1", "external")
edge("G1", "G2", "Для дерева, не являющегося путём, Δ≥3.")
edge("G0", "G3", "Подсчёт степеней и смежности специальных факторов.")
edge("G4", "N2", "Доказывает гипотезу суммированием по n−1 рёбрам.", "context")

node("N3", "metrics", "Предл. 3.7.1", "Компактность и метрика\n[Н: стандартная конструкция]", "novelty",
     "Неверного утверждения не установлено. Суммируемая взвешенная метрика конечного произведения и компактность стандартны; самостоятельный новый результат не обоснован.",
     "с. 88–89", "N3")
node("M1", "metrics", "Предл. 3.8.9", "Сдвиг 2-липшицев\nв метрике d_SL", source="с. 98")
edge("N3", "M1", "Используется определение d_SL; свойство компактности для оценки не требуется.")
node("Q0", "polyomino", "Модель разрезания", "Полные линии сетки;\nбез перемещения частей", "external")
node("Q1", "polyomino", "Теорема 4.2.1", "Минимум разрезов = λ(P)", source="с. 107–108")
edge("Q0", "Q1", "Каждая линия, несущая внутреннее ребро, необходима и достаточна.")

BY_ID = {n["id"]: n for n in NODES}
assert len(BY_ID) == len(NODES)
assert all(e["source"] in BY_ID and e["target"] in BY_ID for e in EDGES)

def quote(s):
    return json.dumps(s, ensure_ascii=False)

def make_dot(groups=None, overview=False):
    chosen = [n for n in NODES if groups is None or n["group"] in groups]
    ids = {n["id"] for n in chosen}
    edges = [e for e in EDGES if e["source"] in ids and e["target"] in ids]
    out = ['digraph dependencies {',
           'graph [rankdir=TB, bgcolor="transparent", compound=true, pad=0.15, '
           'nodesep=0.18, ranksep=0.42, fontname="DejaVu Sans", fontsize=18, '
           'splines=polyline, outputorder=edgesfirst, pack=true, packmode="array_3"];',
           'node [shape=box, style="rounded,filled", fontname="DejaVu Sans", fontsize=12, '
           'fontcolor="#17212B", margin="0.14,0.10", penwidth=1.15];',
           'edge [color="#647488", penwidth=1.05, arrowsize=0.65, '
           'fontname="DejaVu Sans", fontsize=9];']
    for gi, (group, title) in enumerate(GROUPS.items()):
        members = [n for n in chosen if n["group"] == group]
        if not members:
            continue
        out += [f'subgraph cluster_{group} {{',
                f'label={quote(title)}; labelloc=t; labeljust=l; '
                'color="#C8D1DA"; style="rounded"; penwidth=0.8; margin=14;']
        for n in members:
            fill, stroke, code, _ = PALETTE[n["status"]]
            label = f'[{code}] {n["title"]}\n{n["body"]}'
            if n["source"]:
                label += '\n' + n["source"].split(";")[0]
            tooltip = (n["note"] or n["title"]) + (" | " + n["source"] if n["source"] else "")
            attrs = dict(label=label, fillcolor=fill, color=stroke,
                         tooltip=tooltip, id="node-"+n["id"])
            if n["status"] == "external":
                attrs["shape"] = "ellipse"
                attrs["fontsize"] = "11"
            out.append(quote(n["id"]) + ' [' + ", ".join(f'{k}={quote(v)}' for k,v in attrs.items()) + '];')
        # Invisible scaffolding controls placement only. These are NOT logical
        # dependencies and are deliberately excluded from EDGES / JSON.
        levels = {
            "fibonacci": [["B0","B1","B6"],["B5","B2","B3","B4"],["B7"]],
            "palindromes": [["C1","C2","C12"],["C3","C4","C5"],
                            ["C6","C7","C8"],["C9","C10"],["C11"]],
            "twisted": [["D9","D0","D8"],["N1","D1","D2"],
                        ["E5","D5","D3"],["D4","D7"],["D6"]],
            "trees": [["G4","G1","G0"],["N2","G2","G3"]],
        }.get(group, [])
        for level in levels:
            present = [v for v in level if v in ids]
            if present:
                out.append("{rank=same; " + "; ".join(quote(v) for v in present) + ";}")
        for before, after in zip(levels, levels[1:]):
            if before and after:
                out.append(f'{quote(before[0])} -> {quote(after[0])} [style=invis, weight=25];')
        out.append('}')
    for e in edges:
        attrs = dict(tooltip=e["why"], id=f'edge-{e["source"]}-{e["target"]}')
        if e["kind"] == "object":
            attrs.update(color="#C47700", style="dashed", penwidth="1.6")
        elif e["kind"] == "context":
            attrs.update(color="#8054A6", style="dotted", penwidth="1.5")
        out.append(f'{quote(e["source"])} -> {quote(e["target"])} ['+
                   ", ".join(f'{k}={quote(v)}' for k,v in attrs.items())+'];')
    out.append('}')
    return '\n'.join(out)

def render(name, groups=None):
    dot = WORK / f"{name}.dot"
    dot.write_text(make_dot(groups), encoding="utf-8")
    for fmt in ("svg", "pdf"):
        subprocess.run(["dot", f"-T{fmt}", str(dot), "-o", str(WORK/f"{name}.{fmt}")],
                       check=True, capture_output=True)
    return WORK / f"{name}.pdf"

overview = render("overview")
branches = [
    ("preliminary", ["prelim", "factorials"], "Ошибки предварительных утверждений и факториалы"),
    ("fibonacci", ["fibonacci", "palindromes"], "Слово Фибоначчи: плотности и палиндромы"),
    ("twisted", ["twisted"], "Скрученные повторы и динамика"),
    ("trees", ["trees", "metrics", "polyomino"], "Деревья, метрика и разрезания"),
]
for name, groups, title in branches:
    render(name, groups)

font_dir = Path("/usr/share/fonts/truetype/dejavu")
pdfmetrics.registerFont(TTFont("DV", str(font_dir/"DejaVuSans.ttf")))
pdfmetrics.registerFont(TTFont("DVB", str(font_dir/"DejaVuSans-Bold.ttf")))
TEXT = "#17212B"
MUTED = "#516071"

def text(c, x, y, s, size=10, font="DV", color=TEXT):
    c.setFillColor(HexColor(color))
    c.setFont(font, size)
    c.drawString(x, y, s)

def header_pdf(path, size, title, subtitle, footer, legend=True):
    w,h=size; c=canvas.Canvas(str(path), pagesize=size)
    m=26
    text(c,m,h-35,title,20,"DVB")
    text(c,m,h-56,subtitle,10,color=MUTED)
    y=h-80
    if legend:
        items=list(PALETTE.items())
        cols=4 if w>1000 else 2
        cw=(w-2*m)/cols
        for i,(status,(fill,stroke,code,label)) in enumerate(items):
            col=i%cols; row=i//cols
            xx=m+col*cw; yy=y-row*23
            c.setFillColor(HexColor(fill));c.setStrokeColor(HexColor(stroke))
            c.roundRect(xx,yy-12,24,18,3,stroke=1,fill=1)
            text(c,xx+7,yy-7,code,10,"DVB")
            # Short labels for the chart sheet.
            short={
                "ok":"Ошибок не выявлено",
                "local":"Локальная поправка",
                "gap":"Требует восстановления",
                "false":"Неверное утверждение / формула",
                "critical":"Противоречивое определение",
                "novelty":"Новизна / статус (не ложность)",
                "external":"Внешнее основание",
            }[status]
            text(c,xx+31,yy-7,short,9)
        y-=23*((len(items)-1)//cols+1)
    text(c,m,31,footer,8.4,color=MUTED)
    c.setStrokeColor(HexColor("#CAD2DB"));c.line(m,49,w-m,49)
    # Return room reserved for the graph, in PDF top-left coordinates.
    graph_top=h-y+7
    c.showPage();c.save()
    return fitz.Rect(m,graph_top,w-m,h-62)

atlas=fitz.open()
pages=[
    ("overview", overview, (landscape(A1)[0],1180),
     "Зависимости основных утверждений диссертации",
     f"Абдулла Дуаа • редакция 2026 • {len(NODES)} узлов, {len(EDGES)} связей • оценка по рецензии от 17.11.2026"),
]
for name, groups, title in branches:
    pages.append((name, WORK/f"{name}.pdf", landscape(A3), title,
                  "Те же идентификаторы и цвета, что на общей карте; показаны зависимости внутри выбранных разделов."))

for idx,(name, source, size, title, subtitle) in enumerate(pages,1):
    header=WORK/f"{name}-page.pdf"
    footer=("Сплошная стрелка: используется в доказательстве.  Пунктир оранжевый: объект требует правки.  "
            "Точки фиолетовые: сопоставление / уточнение статуса.")
    area=header_pdf(header,size,title,subtitle,footer)
    background=fitz.open(header);chart=fitz.open(source)
    # Draw the chart first and the independent page furniture above it.
    # This keeps the legend readable even with an opaque Graphviz background.
    composed=fitz.open()
    page=composed.new_page(width=size[0],height=size[1])
    page.show_pdf_page(area,chart,0,keep_proportion=True)
    page.show_pdf_page(page.rect,background,0,keep_proportion=True)
    atlas.insert_pdf(composed)
    composed.close()
    chart.close();background.close()

# Explanatory appendix, two A4 pages, with non-ambiguous scopes of severity.
notes_path=WORK/"notes.pdf"
c=canvas.Canvas(str(notes_path),pagesize=A4)
W,H=A4
style=ParagraphStyle("p",fontName="DV",fontSize=10.1,leading=14.4,
                     textColor=HexColor(TEXT),spaceAfter=5)
small=ParagraphStyle("small",parent=style,fontSize=9.2,leading=12.9)
y=H-40

def para(s, x=33, width=W-66, style_=style, gap=7):
    global y
    p=Paragraph(s,style_);pw,ph=p.wrap(width,H)
    p.drawOn(c,x,y-ph);y-=ph+gap

def note_head(title, number):
    global y
    y=H-38;text(c,33,y,title,15,"DVB");y-=26
    text(c,33,22,f"Приложение {number} • Граф зависимостей • 17.11.2026",8,color=MUTED)

note_head("Как читать граф и шкалу ошибок",1)
para("Карта охватывает основные теоретические ветви и все математические замечания предыдущей рецензии. "
     "Это экспертная реконструкция зависимостей, а не машинная формальная верификация всех доказательств рукописи. "
     "Объединённые узлы явно содержат несколько номеров. Педагогический эксперимент и часть вспомогательных утверждений не включены.")
para("Показаны основные доказательства; часть альтернативных выводов и элементарных исходных фактов опущена.",
     style_=small)
para("<b>Стрелка A → B</b> означает, что A используется для доказательства B или задаёт его объект. "
     "Фиолетовые точечные связи имеют только библиографический / оценочный смысл. "
     "Отсутствие стрелки из ошибочного узла означает, что использования в показанных доказательствах не обнаружено.")
para("<b>Цвет оценивает локальный дефект и необходимый ремонт.</b> Красный узел не означает, "
     "что все результаты диссертации опровергнуты. Зелёный означает лишь отсутствие обнаруженной ошибки в рассмотренном фрагменте.")

for key in ("E3","A1","E4","E1","E2","E5","C4"):
    n=BY_ID[key];fill,stroke,code,label=PALETTE[n["status"]]
    c.setFillColor(HexColor(fill));c.setStrokeColor(HexColor(stroke))
    c.roundRect(33,y-17,27,20,3,stroke=1,fill=1);text(c,42,y-12,code,10,"DVB")
    text(c,68,y-12,n["title"]+" • "+n["source"].split(";")[0],10,"DVB")
    y-=28
    para(escape(n["note"]),style_=small,gap=10)

c.showPage()
note_head("Область влияния и замечания к статусу",2)
para("<b>1. Основные новые результаты.</b> Для теоремы 3.8.5 отмечена локальная поправка доказательства, "
     "не меняющая κ. В теореме 5.1.3 обнаруженных математических ошибок нет. "
     "Из красного определения 3.1.2 нет выявленного пути к этим теоремам.")
para("<b>2. Зависимость, требующая восстановления.</b> Определение 3.1.2 задаёт последовательность "
     "для леммы 3.1.1. Пока начальные условия противоречивы, лемма не имеет однозначно определённого объекта. "
     "После исправления определения формулу (3.11) следует проверить заново.")
para("<b>3. Два разных утверждения о log(n!).</b> Ошибочно отрицание равномерного распределения "
     "в вводном абзаце. Лемма 2.2.1 утверждает только бесконечное число попаданий в любой интервал "
     "и имеет отдельное элементарное доказательство. От ошибочного абзаца стрелки к лемме нет.")
para("<b>4. Динамика не зависит от наблюдения 3.8.3.</b> Верхняя оценка сложности "
     "в теореме 3.8.7(3) получается непосредственно из блочной структуры. "
     "Для неё не требуется экспериментальная закономерность первых разностей p(n).")
para("<b>5. Дополнительная локальная поправка при составлении графа.</b> В лемме 3.6.2 "
     "вложенность yₙ в yₙ₊₁ начинается с n=1: y₀=01 и y₁=02. "
     "Для теоремы о богатстве начальный случай y₀ проверяется отдельно. Предельная конструкция не меняется.",
     style_=small)
for key in ("N1","N2","N3"):
    n=BY_ID[key]
    para("<b>Н • "+escape(n["title"])+".</b> "+escape(n["note"]),style_=small)
para("<b>Для гипотезы о звезде:</b> если T не звезда, то Δ≤n−2 и каждое из n−1 рёбер "
     "даёт вклад не более Δ²−1. Поэтому irr₂(T)≤(n−1)((n−2)²−1)&lt;(n−1)((n−1)²−1)=irr₂(Sₙ).",style_=small)
para("<b>Основания карты.</b> Представленные document.tex / document.pdf и ранее подготовленная рецензия. "
     "Страницы на узлах — печатные страницы рукописи. "
     "В машиночитаемых данных для каждой связи сохранено объяснение её основания.",style_=small)
para("<b>Литературные ориентиры:</b> Fischler (2006), <i>Palindromic prefixes and episturmian words</i>; "
     "Blondin-Massé et al. (2007), DOI 10.46298/dmtcs.397; Diaconis (1977), DOI 10.1214/aop/1176995891; "
     "Adamczewski–Allouche (2007), DOI 10.1016/j.tcs.2007.03.017; "
     "Tromp–Shallit (1995), DOI 10.1016/0020-0190(95)00074-M.",style_=small)
c.showPage();c.save()
notes=fitz.open(notes_path);atlas.insert_pdf(notes);notes.close()
atlas.set_metadata({"title":"Граф зависимостей утверждений и карта ошибок",
                    "subject":"Диссертация Абдуллы Дуаа, 2026; экспертная оценка",
                    "author":"", "keywords":"dependency graph, mathematics, review"})
atlas.save(ROOT/"dependency_graph.pdf",garbage=4,deflate=True)
atlas.close()

# Standalone SVG: include a legend and preserve the original Graphviz tooltips.
svg_ns="http://www.w3.org/2000/svg"
ET.register_namespace("",svg_ns)
ET.register_namespace("xlink","http://www.w3.org/1999/xlink")
svg=ET.fromstring((WORK/"overview.svg").read_text())
vb=[float(v) for v in svg.attrib["viewBox"].split()]
sw,sh=vb[2],vb[3]
extra=138
svg.set("viewBox",f"0 0 {sw} {sh+extra}")
svg.set("width",str(sw));svg.set("height",str(sh+extra))
children=list(svg)
for ch in children:svg.remove(ch)
ET.SubElement(svg,f"{{{svg_ns}}}rect",{"width":str(sw),"height":str(sh+extra),"fill":"white"})
def svg_text(x,y,s,fs=16,weight="normal"):
    t=ET.SubElement(svg,f"{{{svg_ns}}}text",{"x":str(x),"y":str(y),"font-family":"DejaVu Sans, sans-serif",
                     "font-size":str(fs),"font-weight":weight,"fill":TEXT});t.text=s
svg_text(18,29,"Зависимости основных утверждений: 52 узла, 42 связи",22,"bold")
svg_text(18,51,"Сплошная стрелка: используется в доказательстве. Цвет — локальная оценка, не итог всей работы.",14)
for i,(status,(fill,stroke,code,label)) in enumerate(PALETTE.items()):
    x=18+(i%4)*(sw-36)/4;y=72+(i//4)*28
    ET.SubElement(svg,f"{{{svg_ns}}}rect",{"x":str(x),"y":str(y),"width":"23","height":"20",
                  "rx":"3","fill":fill,"stroke":stroke})
    svg_text(x+6,y+15,code,13)
    short={"ok":"Ошибок не выявлено","local":"Локальная поправка","gap":"Требует восстановления",
           "false":"Неверное утверждение / формула","critical":"Противоречивое определение",
           "novelty":"Новизна / статус, не ложность","external":"Внешнее основание"}[status]
    svg_text(x+31,y+15,short,14)
group=ET.SubElement(svg,f"{{{svg_ns}}}g",{"transform":f"translate(0 {extra})"})
for ch in children:group.append(ch)
(ROOT/"dependency_graph.svg").write_text(ET.tostring(svg,encoding="unicode"),encoding="utf-8")
(ROOT/"dependency_graph.dot").write_text(make_dot(),encoding="utf-8")
manifest={"scope":"Основные теоретические утверждения; не полная формальная верификация",
          "date":"2026-11-17","palette":PALETTE,"groups":GROUPS,"nodes":NODES,"edges":EDGES}
(ROOT/"dependency_graph.json").write_text(json.dumps(manifest,ensure_ascii=False,indent=2),encoding="utf-8")

# Preview of the first sheet. The PDF and SVG remain scalable.
doc=fitz.open(ROOT/"dependency_graph.pdf")
pix=doc[0].get_pixmap(matrix=fitz.Matrix(1,1),alpha=False)
pix.save(ROOT/"dependency_graph.png")
print(json.dumps({"nodes":len(NODES),"edges":len(EDGES),"pages":len(doc),
                  "preview":[pix.width,pix.height],
                  "source_graph_page":list(fitz.open(overview)[0].rect)},ensure_ascii=False))
doc.close()

readme="""Граф зависимостей утверждений и карта ошибок
Диссертация Абдуллы Дуаа, представленная редакция 2026 года.
Дата экспертной оценки: 17 ноября 2026 года.

dependency_graph.pdf — общая карта, 4 подробных листа и 2 страницы пояснений.
dependency_graph.svg — масштабируемая общая карта; подсказки на узлах.
dependency_graph.png — предварительный просмотр.
dependency_graph.dot — редактируемый исходник Graphviz.
dependency_graph.json — узлы, оценки, связи и объяснения их оснований.
build_graph.py — программа сборки (Python, Graphviz, PyMuPDF, ReportLab).

Сплошные стрелки: использование в доказательстве.
Оранжевый пунктир: зависимость от определения, которое требуется восстановить.
Фиолетовые точки: литературное сопоставление или уточнение статуса.

Шкала: 0 — ошибок не выявлено; 1 — локальная поправка;
2 — обоснование / объект требует восстановления;
3 — неверное утверждение / формула; 4 — противоречивое определение.
Н — замечание к новизне или статусу, не к истинности.
И — внешнее основание или отдельное рассуждение рецензента.

Оценки локальны. Карта не является полной формальной верификацией диссертации.
"""
(ROOT/"README.txt").write_text(readme,encoding="utf-8")
with zipfile.ZipFile(ROOT/"dependency_graph_bundle.zip","w",zipfile.ZIP_DEFLATED) as z:
    for name in ("dependency_graph.pdf","dependency_graph.svg","dependency_graph.png",
                 "dependency_graph.dot","dependency_graph.json","build_graph.py","README.txt"):
        z.write(ROOT/name,arcname=name)
