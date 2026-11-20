# Исправленная редакция работы

Содержимое подготовлено 17 ноября 2026 года.

- **thesis_corrected.pdf** — полная работа с внесёнными математическими исправлениями.
- **thesis_corrected.tex** — полный исходник этой редакции; формулировки и доказательства встроены в текст.
- **mathematical_corrections.pdf** — отдельный законченный текст исправленных формулировок и доказательств критических узлов.
- **mathematical_corrections.tex** — его самодостаточный исходник.
- **CHANGELOG.md** — соответствие замечаний и внесённых исправлений.
- **changes.diff** — точные изменения относительно исходной рукописи.
- **verify_corrections.py**, **verification_results.json** — конечные проверки и результаты.
- **original_source/document.tex** — неизменённая исходная версия для сравнения.
- **repair_*.tex**, **apply_corrections.py** — блоки исправлений и программа их применения.
- PDF-рисунки и необходимые пакеты оформления находятся рядом с основными исходниками.

## Сборка

Нужны XeLaTeX (TeX Live / MiKTeX), поддержка русского языка и шрифты
Liberation Serif / Liberation Sans / DejaVu Sans Mono. Запускайте из этой папки:

~~~sh
xelatex -interaction=nonstopmode -halt-on-error thesis_corrected.tex
xelatex -interaction=nonstopmode -halt-on-error thesis_corrected.tex
xelatex -interaction=nonstopmode -halt-on-error mathematical_corrections.tex
xelatex -interaction=nonstopmode -halt-on-error mathematical_corrections.tex
~~~

При изменении оглавления может потребоваться третий запуск.
Библиография включена в исходники; BibTeX и внешние базы не нужны.

Для воспроизведения редакционных замен и конечных проверок:

~~~sh
python3 apply_corrections.py
python3 verify_corrections.py
~~~

Нормировка общего семейства последовательностей и классический вход
в доказательство штурмовых индексов явно описаны в CHANGELOG.md.
Редакция закрывает перечисленные в нём замечания; вычислительные
проверки не объявляются заменой математических доказательств.
