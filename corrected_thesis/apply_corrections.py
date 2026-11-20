#!/usr/bin/env python3
"""Create a corrected copy without overwriting the uploaded source."""
from pathlib import Path
import re
import difflib

HERE=Path(__file__).resolve().parent
SRC=HERE/"original_source"/"document.tex"
original=SRC.read_text(encoding="utf-8")
s=original

def once(old,new):
    global s
    if s.count(old)!=1:
        raise ValueError(f"Expected one occurrence, got {s.count(old)}: {old[:100]!r}")
    s=s.replace(old,new,1)

def block(start,end,filename):
    global s
    a=s.index(start);b=s.index(end,a)
    s=s[:a]+(HERE/filename).read_text(encoding="utf-8").rstrip()+"\n\n"+s[b:]

# Modern Unicode engine and an explicitly available Cyrillic text font.
preamble=r"""\usepackage{fontspec}
\defaultfontfeatures{Ligatures=TeX}
\setmainfont{Liberation Serif}
\setsansfont{Liberation Sans}
\setmonofont{DejaVu Sans Mono}[Scale=MatchLowercase]
\usepackage{polyglossia}
\setdefaultlanguage{russian}
\setotherlanguage{english}
\usepackage{needspace}
\newfontfamily\cyrillicfont{Liberation Serif}
\newfontfamily\cyrillicfontsf{Liberation Sans}
\newfontfamily\cyrillicfonttt{DejaVu Sans Mono}[Scale=MatchLowercase]"""
once(r"""\usepackage{cmap}
\usepackage[T2A]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{mathtext}
\usepackage[russian]{babel}""",preamble)
once(r"\addto\captionsrussian{\renewcommand{\proofname}{Доказательство}}",
     r"\gappto\captionsrussian{\renewcommand{\proofname}{Доказательство}}")
once(r"\newtheorem{proposition}[theorem]{Предложение}",
     r"\newtheorem{proposition}[theorem]{Предложение}"+"\n"+
     r"\newtheorem*{proposition*}{Предложение}")
s="% !TeX program = xelatex\n% Математические исправления: 17.11.2026; подробности в CHANGELOG.md.\n"+s
# The uploaded source never uses a stmaryrd symbol.
s=s.replace(r"\usepackage{stmaryrd}","% stmaryrd: не используется в данном исходнике.")
# Replace Babel-specific discretionary dashes with portable TeX dashes.
s=s.replace('"---','---')
# Front matter has Roman numbering; the main text starts at Introduction, page 1.
once(r"""\pagenumbering{roman}
	%\tableofcontents
	\clearpage
	
	\pagenumbering{arabic}""",
     r"""\pagenumbering{roman}
    \hypersetup{pageanchor=false}""")
once(r"\end{titlepage}",r"\end{titlepage}"+"\n"+r"\hypersetup{pageanchor=true}")
once(r"""\tableofcontents
	\newpage
	\pagenumbering{arabic}""",
     r"""\tableofcontents
    \newpage""")
once(r"\chapter*{Введение}",r"\pagenumbering{arabic}"+"\n"+r"\chapter*{Введение}")

# Correct the definition of equidistribution: count indices, including repetitions.
once(r"\frac{\#\bigl(\{s_{1},\dots,s_{n}\} \cap [c,d]\bigr)}{n}",
     r"\frac{\#\{1\le j\le n:\ c\le s_j\le d\}}{n}")
block("Эти понятия использовались для получения глубоких результатов",
      r"\begin{lemma}\label{lem:lead}","repair_equdistribution.tex")

# Correct the binomial identity and give a short independent proof.
old=r"""F_n = \sum_{k=0}^{\left\lfloor \frac{n}{2} \right\rfloor} \binom{n-k}{k}.
\end{equation}
Обобщения"""
new=r"""F_{n+1} = \sum_{k=0}^{\left\lfloor \frac{n}{2} \right\rfloor} \binom{n-k}{k}.
\end{equation}
Здесь $F_0=0$, $F_1=1$; первая формула записана при $n\ge1$,
вторая --- при $n\ge0$.
Действительно, число способов покрыть отрезок из $m$ клеток
плитками длин $1$ и $2$ удовлетворяет рекурсии Фибоначчи
с начальными значениями $1,1$, то есть равно $F_{m+1}$.
При ровно $k$ плитках длины $2$ всего имеется $m-k$ плиток;
выбор мест для длинных плиток даёт $\binom{m-k}{k}$.
Суммирование по $k$ доказывает вторую формулу, а замена $m=n-1$
--- первую.
Обобщения"""
once(old,new)
block("На основе~\\eqref{eq1pirl} были введены различные обобщения",
      "Многие из последовательностей, рассматриваемых в этом контексте",
      "repair_recurrence_definition.tex")
block(r"\begin{lemma}[\cite{Mehraban2006Gulliver}]\label{lemgenn1}",
      "Слово Фибоначчи является прототипическим штурмовым словом",
      "repair_generating_function.tex")
block("Слово Фибоначчи является прототипическим штурмовым словом",
      "Бесконечное слово Фибоначчи, получаемое как предел стандартных",
      "repair_sturmian_indices.tex")

# Local corrections needed to keep the surrounding arguments coherent.
once("Слова $y_n$ являются префиксами слов $y_{n+1}$, и",
     "При $n\\ge1$ слова $y_n$ являются префиксами слов $y_{n+1}$, и")
once("Равенство $y_{n+1}=y_ny_{n-1}$ показывает, что",
     "При $n\\ge1$ равенство $y_{n+1}=y_ny_{n-1}$ показывает, что")
once(r"$y_n=\iota_0(x_n)$, где $x_n=\rho(s_{n-1})$ (лемма~\ref{lem:Ystructure}), --- переименование префикса слова Фибоначчи, $|x_n|=F_{n+1}$.",
     r"""При $n=0$ имеем $y_0=01$: его непустые палиндромные факторы
суть $0$ и $1$, поэтому оно богато.
Пусть теперь $n\ge1$. Тогда $y_n=\iota_0(x_n)$, где
$x_n=\rho(s_{n-1})$ (лемма~\ref{lem:Ystructure}), ---
переименование префикса слова Фибоначчи, $|x_n|=F_{n+1}$.""")
once(r"Если $j'\ge b$, то $\lfloor 2b/j'\rfloor\le1$, так",
     r"Если $j'\ge b$, то $\lfloor 2b/j'\rfloor\le2$, так")

# A true elementary assertion is presented with its proof, not as an open problem.
start=r"\begin{conjecture}"
a=s.index(start,s.index(r"\subsection{Общие результаты}"))
b=s.index("%----------------------------------------",a)
replacement=r"""\Needspace{7\baselineskip}
\begin{proposition*}[Максимальность индекса звезды]
Для каждого дерева $T$ на $n\ge3$ вершинах, не изоморфного звезде $S_n$,
выполняется
\[
 \operatorname{irr}_2(T)<\operatorname{irr}_2(S_n)=n(n-1)(n-2).
\]
\end{proposition*}
\begin{proof}
Если $T$ не является звездой, его максимальная степень
$\Delta\le n-2$. Для любого ребра $uv$ степени его концов
лежат между $1$ и $\Delta$, поэтому
$|d_u^2-d_v^2|\le\Delta^2-1$.
Так как в дереве $n-1$ ребро, получаем
\[
 \operatorname{irr}_2(T)\le(n-1)(\Delta^2-1)
 \le(n-1)((n-2)^2-1)
 <(n-1)((n-1)^2-1).
\]
Последнее выражение равно индексу звезды.
Если для данного $n$ незвезды не существует, утверждение выполняется
в силу пустоты рассматриваемого класса.
\end{proof}
"""
s=s[:a]+replacement+"\n"+s[b:]
old="Оценка $\\operatorname{irr}_2(T)<\\operatorname{irr}_2(S_n)$ для деревьев, отличных от звезды, проверенная при $n\\le12$, высказана в виде гипотезы в главе~5, а зависимость инвариантов деревьев факторов от последующих неполных частных углового коэффициента не описана."
new="Максимальность $\\operatorname{irr}_2(S_n)$ среди деревьев на $n$ вершинах доказана в главе~5. Зависимость более тонких графовых инвариантов от последующих неполных частных углового коэффициента остаётся предметом дальнейшего исследования."
once(old,new)

# Correct the literature status of the complexity observation.
once(r"\begin{observation}[Факторная сложность]",
     r"\begin{observation}[Факторная сложность; сопоставление с известным результатом]")
anchor="В частности, $p(k)$ не имеет вида $(N-1)k+C_N$, в отличие от слов Арну--Ози; при $N=2$ (Туэ--Морс) разности равны $2$ и $4$."
once(anchor,anchor+"\n"+
     r"Полная функция сложности слова $s_2(n)\bmod N$ вычислена Тромпом и Шаллитом~\cite{TrompShallit1995}. Поэтому эта закономерность рассматривается как иллюстрация известного результата, а не как самостоятельная открытая задача.")
once(r"\item доказательство закономерности $p(k+1)-p(k)\in\{N(N-1),N^2\}$, наблюдавшейся выше, и сравнение с известной сложностью слова Туэ--Морса;",
     r"\item исследование сложности языков для более общих перестановочных ограничений; классическая сложность $s_2(n)\bmod N$ при этом уже известна~\cite{TrompShallit1995};")
once(r"Точная закономерность $p(k+1)-p(k)\in\{N(N-1),N^2\}$ для сложности факторов слова $W_{A,\sigma,a_0}$ наблюдается, но не доказана, а сильная $(k,\delta)$-свобода для перестановок $\delta$, не являющихся степенями $\sigma$, не рассматривается",
     r"Факторная сложность $W_{A,\sigma,a_0}$ сопоставлена с известным результатом Тромпа--Шаллита~\cite{TrompShallit1995}; сильная $(k,\delta)$-свобода для перестановок $\delta$, не являющихся степенями $\sigma$, не рассматривается")

# Correct one bibliographic date and add the precise sources used in the repairs.
once("Mehraban E., Gulliver T.A., Hincal E. Blind signatures from the generalized $(t,k)$-Fibonacci $p$-sequences // J. Dyn. Games. 2006. Vol. 13. P. 193--203.",
     "Mehraban E., Gulliver T.A., Hincal E. Blind signatures from the generalized $(t,k)$-Fibonacci $p$-sequences // J. Dyn. Games. 2026. Vol. 13. P. 193--203. DOI: 10.3934/jdg.2025022.")
bib=r"""
\bibitem{Diaconis1977}
Diaconis P. The distribution of leading digits and uniform distribution mod~1 //
Ann. Probab. 1977. Vol.~5, No.~1. P.~72--81. DOI: 10.1214/aop/1176995891.
\bibitem{DamanikLenz2002}
Damanik D., Lenz D. The index of Sturmian sequences //
European J. Combin. 2002. Vol.~23. P.~23--29. DOI: 10.1006/eujc.2000.0496.
\bibitem{Peltomaki2015}
Peltomäki J. Characterization of repetitions in Sturmian words: A new proof //
Inform. Process. Lett. 2015. Vol.~115, No.~11. P.~886--891.
DOI: 10.1016/j.ipl.2015.05.011.
\bibitem{AdamczewskiAllouche2007}
Adamczewski B., Allouche J.-P. Reversals and palindromes in continued fractions //
Theoret. Comput. Sci. 2007. Vol.~380. P.~220--237.
DOI: 10.1016/j.tcs.2007.03.017.
\bibitem{TrompShallit1995}
Tromp J., Shallit J. Subword complexity of a generalized Thue--Morse word //
Inform. Process. Lett. 1995. Vol.~54, No.~6. P.~313--316.
DOI: 10.1016/0020-0190(95)00074-M.
"""
once(r"\end{thebibliography}",bib+"\n"+r"\end{thebibliography}")
once(r"\usepackage[hidelinks]{hyperref}",
     r"""\usepackage[unicode,hidelinks]{hyperref}
\hypersetup{pdftitle={Комбинаторика слов и символическая динамика: исправленная редакция},
pdfauthor={Абдулла Дуаа},
pdfsubject={Редакция с математическими исправлениями от 17.11.2026}}""")
once(r"\subsection{Основание $b$ и произвольное $k$: скрученный критический показатель}",
     r"\subsection{\texorpdfstring{Основание $b$ и произвольное $k$: скрученный критический показатель}{Основание b и произвольное k: скрученный критический показатель}}")
once(r"\subsection{Динамические свойства слова $W^{(b)}$}",
     r"\subsection{\texorpdfstring{Динамические свойства слова $W^{(b)}$}{Динамические свойства слова W(b)}}")

# Layout repairs preserve the mathematical content.
once(r"\usepackage{algpseudocode}",
     r"\usepackage{algpseudocode}"+"\n"+r"\algrenewcommand\textproc{\textnormal}")
once(r"text width=1.75cm",r"text width=2.35cm")
once(r"""1, & \text{если } u[k+j-1] = v[j] \text{ и }  1 \le k + j - 1 \le n  \text{ для всех } j \in \{1,\ldots,m\}""",
     r"""1, & \text{если } k+m-1\le n\ \text{и }u[k\ldots k+m-1]=v""")
once(r"s_0=0,\ s_1=01,\ s_2=010,\ s_3=01001,\ s_4=01001010,\ s_5=0100101001001,\ \dots",
     r"""\begin{aligned}
 &s_0=0,\quad s_1=01,\quad s_2=010,\quad s_3=01001,\\
 &s_4=01001010,\quad s_5=0100101001001,\quad\dots
\end{aligned}""")
once(r"|V(T_n)|=\frac{(n+1)(n+2)}2,\qquad \operatorname{irr}(T_n)=4n-2d,\qquad \operatorname{irr}_2(T_n)=18n-10d-2,",
     r"""\begin{aligned}
 |V(T_n)|&=\frac{(n+1)(n+2)}2,\\
 \operatorname{irr}(T_n)&=4n-2d,\qquad
 \operatorname{irr}_2(T_n)=18n-10d-2.
\end{aligned}""")
# Keep these two tables within the text block.
a=s.index(r"\label{table:magic_triangle}");b=s.index(r"\end{table}",a)
s=s[:a]+s[a:b].replace(r"{0.60\textwidth}",r"{0.59\textwidth}")+s[b:]
a=s.index(r"\label{tab:descriptive}");b=s.index(r"\end{table}",a)
s=s[:a]+s[a:b].replace(r"\setlength{\tabcolsep}{4pt}",r"\setlength{\tabcolsep}{2pt}")+s[b:]
# Scale only the wide Monty Hall decision tree.
label=s.index(r"\label{fign3}")
a=s.rfind(r"\begin{tikzpicture}",0,label);b=s.index(r"\end{tikzpicture}",a)+len(r"\end{tikzpicture}")
s=s[:a]+r"\resizebox{0.96\linewidth}{!}{%"+"\n"+s[a:b]+"\n}"+s[b:]

# A concise revision stamp avoids confusing this file with the uploaded edition.
once(r"{\large 1.1.5 Математическая логика, алгебра, теория чисел и дискретная математика \par}",
     r"{\large 1.1.5 Математическая логика, алгебра, теория чисел и дискретная математика \par}"
     "\n"+r"\vspace{0.4cm}{\small Редакция с математическими исправлениями от 17.11.2026\par}")

(HERE/"thesis_corrected.tex").write_text(s,encoding="utf-8")
diff="".join(difflib.unified_diff(original.splitlines(keepends=True),s.splitlines(keepends=True),
             fromfile="original/document.tex",tofile="corrected/thesis_corrected.tex"))
(HERE/"changes.diff").write_text(diff,encoding="utf-8")

# Standalone first-stage deliverable: reformulations and proofs, in reading order.
head=r"""\documentclass[12pt,a4paper]{article}
\usepackage[margin=24mm]{geometry}
\usepackage{fontspec}
\defaultfontfeatures{Ligatures=TeX}
\setmainfont{Liberation Serif}
\setsansfont{Liberation Sans}
\usepackage{polyglossia}
\setdefaultlanguage{russian}
\setotherlanguage{english}
\newfontfamily\cyrillicfont{Liberation Serif}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{microtype}
\usepackage[unicode,hidelinks]{hyperref}
\newtheorem{theorem}{Теорема}[section]
\newtheorem{lemma}{Лемма}[section]
\newtheorem{definition}{Определение}[section]
\setlength{\emergencystretch}{3em}
\setlength{\parskip}{3pt}
\linespread{1.05}
\begin{document}
\begin{center}
{\LARGE\bfseries Исправленные формулировки и доказательства\par}
\medskip
{\large Комбинаторика слов и символическая динамика\par}
\medskip
17 ноября 2026 года
\end{center}
Этот текст содержит законченные замены красных, оранжевых и янтарных
узлов экспертной карты. Они также внесены в полную исправленную
редакцию диссертации. Номера утверждений в этом отдельном документе
локальны; соответствие исходной рукописи указано в заголовках разделов.
Исправление определения семейства не единственно: выбрана нормировка,
сохраняющая при $p=1$ исходную производящую функцию и порядок $k$.
Классическая классификация штурмовых степеней явно указана как
внешний результат; вывод асимптотического показателя из неё дан ниже.
\section{Равномерное распределение: исходная лемма 2.2.1}
\begin{theorem}[Критерий Вейля]
Последовательность $(x_n)$ равномерно распределена по модулю $1$
тогда и только тогда, когда для каждого целого $h\ne0$
$N^{-1}\sum_{n=1}^N\exp(2\pi\mathrm i h x_n)\to0$.
\end{theorem}
"""
note=head+(HERE/"repair_equdistribution.tex").read_text()
note+=r"\section{Согласованная рекурсия: исходное определение 3.1.2}"+"\n"
note+=(HERE/"repair_recurrence_definition.tex").read_text()
note+=r"\section{Производящая функция: исходная лемма 3.1.1}"+"\n"
note+=(HERE/"repair_generating_function.tex").read_text()
note+=r"\section{Индексы штурмовых слов: исходная теорема 3.1.1}"+"\n"
note+=(HERE/"repair_sturmian_indices.tex").read_text()
note+=r"\begin{thebibliography}{9}"+"\n"+bib+r"\bibitem{Mehraban2006Gulliver}"+\
     "Mehraban E., Gulliver T.A., Hincal E. Blind signatures from the generalized "\
     "$(t,k)$-Fibonacci $p$-sequences // J. Dyn. Games. 2026. Vol.~13. P.~193--203. "\
     "DOI: 10.3934/jdg.2025022.\n"+r"\end{thebibliography}"+"\n"+r"\end{document}"+"\n"
(HERE/"mathematical_corrections.tex").write_text(note,encoding="utf-8")
print("Created corrected thesis and standalone proof document.")
print("Changed lines in unified diff:",len(diff.splitlines()))
