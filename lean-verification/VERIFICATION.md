# Формальная верификация диссертации

Нумерация новизны и положений защиты в таблице соответствует введению исправленной диссертации. [Текст диссертации](../corrected_thesis/thesis_corrected.tex)

Граф построен по исправленному TeX. Рамка каждого узла показывает статус проверки в Lean. В таблице узлов даны непосредственные предпосылки, ссылки на формулировки и теоремы Lean, а также схемы по разделам. [Полный граф (SVG)](verification-graph/verification_graph.svg) · [Таблица и легенда](verification-graph/coverage.md)

Зависимости и метки введения редактируются в [graph.json](verification-graph/graph.json), статусы и ссылки на доказательства — в [status.json](verification-graph/status.json). Команда `python3 verification-graph/build.py` из `lean-verification/` проверяет привязки к исходникам и пересобирает схемы и таблицу. Для SVG нужен Graphviz (`dot`).

| Утверждение | Источник | Граф | Статус Lean |
|---|---|---|---|
| Неподвижная точка обобщённой подстановки, классификация сильных скрученных повторов, бинарное следствие | Новизна 1, защита 1, §3.8, `tw:main`, `avoidance` | [Классификация](verification-graph/coverage.md#node-tw-main) · [Двоичный случай](verification-graph/coverage.md#node-avoidance) | Доказаны формула суммы цифр, периодический и непериодический случаи классификации и бинарный критерий для кубов. Начальное слово задано и на исходном алфавите через итерации подстановки. Блочное определение сильного повтора сведено к сравнению соседних блоков для всех целых показателей перестановки |
| Минимальность, нулевая энтропия, строгая эргодичность | Новизна 1, защита 1, `thm:dynWb` | [Динамика](verification-graph/coverage.md#node-thm-dynwb) | Доказаны разбиение на выровненные блоки, примитивность с порогом N−1, неподвижность слова, равномерная рекуррентность и отсутствие финального периода в заявленном случае. Для одностороннего замыкания орбиты доказаны минимальность, обе оценки сложности при положительной длине и нулевая топологическая энтропия в определении mathlib. Проверены фильтр корней из единицы, оценка ошибки на произвольном окне и равномерная частота 1/N каждой буквы по всему замыканию орбиты. Доказано равенство языков факторов. Выведено следствие об отсутствии длинных скрученных повторов. Построена инвариантная вероятностная мера. Доказаны эквивалентность её единственности и равномерности частот всех факторов и используемый случай теоремы Мишеля для примитивных подстановок постоянной длины. Все пять пунктов, включая строгую эргодичность, объединены в `finiteWord_dynamics` |
| Формулы индексов дерева факторов и число вершин | Новизна 2, защита 3, `thm:factortree` | [Индексы](verification-graph/coverage.md#node-thm-factortree) | Для дерева факторов доказаны число вершин, все пять подсчётов по парам степеней, оба индекса Альбертсона и оба индекса Загреба. Проверены четыре строки таблицы для глубины 8 и построены характеристические слова, реализующие каждую строку. Доказан частный случай слова Фибоначчи. Свойства F1 (сложность k+1) и F2 (обращение префикса) доказаны из механического определения характеристического слова. Итоговая теорема использует исходные условия о наклоне, начальной серии и глубине. Доказано, что граф является деревом в `SimpleGraph` и что подсчёты предшествующего доказательства дают индексы по его степеням |
| Точная погрешность плотности в обрамлённых словах и числовая таблица | Новизна 3, §3.5, `thm1Asymptotic` | [Плотности](verification-graph/coverage.md#node-thm1asymptotic) · [Таблица](verification-graph/coverage.md#node-tab002densitiesasm) | Доказаны формулы длины и числа букв, точные ошибки по Бине, односторонность обрамлённого случая и чередование знака необрамлённого, оценки скоростей и пределы плотностей. Точные равенства для обеих вещественных плотностей собраны в `golden_framed_densities_exact`, а обе оценки скорости записаны в нотации `IsBigO`. Проверены шесть конечных строк таблицы и округления всех четырёх столбцов предельной строки |
| Богатство факторов трёхбуквенного слова | Новизна 4, защита 2, `thm:Yrich` | [Богатство](verification-graph/coverage.md#node-thm-yrich) | Для обеих механических форм штурмова слова доказано богатство каждого фактора при любом сдвиге. Авторский вывод применяет эту теорему к переименованным префиксам Фибоначчи, обрамляет их разделителем и переходит к факторам. Для y₀ явно перечислены два палиндрома. Для любого богатого бесконечного слова доказано следствие о вставке разделителя |
| Инвариантность палиндромной плотности при вставке разделителя | Новизна 4, защита 2, `prop:insertion` | [Вставка](verification-graph/coverage.md#node-prop-insertion) | Доказано равенство вещественных плотностей через совпадение строгих рациональных нижних сечений, включая случай конечного числа префиксов |
| Дихотомия палиндромной плотности, явные значения и диофантовы и теоретико-мерные следствия | Новизна 4, защита 2, `prop:dichotomy`, `cor:palSturm` | [Дихотомия](verification-graph/coverage.md#node-prop-dichotomy) · [Следствия](verification-graph/coverage.md#node-cor-palsturm) | На уровне формулы Фишлера для характеристических штурмовых слов доказаны дихотомия, диофантов критерий, обе границы плотности, спектральный разрыв и точное условие для максимума. Формула Фишлера доказана для механического характеристического слова: рекорды дробных частей отождествлены со всеми блоками промежуточных подходящих дробей, включая два начальных блока, а из этих блоков получены отношения длин. Критерий по наклону, явные значения и эффект вставки выражены для вещественной плотности самого слова из определения в TeX. Связь с инвариантностью при вставке разделителя проверена. Множество исключительных наклонов отождествлено с множеством плохо приближаемых чисел на (0,1). Почти всюду плотность равна 1/2, а исключительное множество имеет нулевую меру Лебега и хаусдорфову размерность 1. Доказаны обе классические метрические предпосылки, которые использует следствие |
| Палиндромная плотность m-боначчи слов | Новизна 4, защита 2, `prop:mbonacci` | [Плотность](verification-graph/coverage.md#node-prop-mbonacci) | Из цитируемой рекурсии Фишлера для перечисления палиндромных префиксов доказаны рост разностей, положительность коэффициента при βₘⁱ, предел отношений длин βₘ и плотность 1/βₘ. Доказано убывание этих плотностей до 1/2. Проверены значение 1/φ при m=2 и рациональные границы для численных примеров, включая округления плотностей 0,5437 и 0,5188. Для β₄ строго доказано 1,92756 < β₄ < 1,92757, так что 1,9276 в исходнике представляет округление. Для самого стандартного слова с циклической директивой из палиндромных замыканий доказано, что их длины исчерпывают все палиндромные префиксы. Из предыдущего вхождения директивной буквы получена нужная рекурсия. Доказано вещественное равенство плотности 1/βₘ, включая численные примеры и убывающий предел |
| Биномиальные подсчёты, точные плотности, логарифмический предел | Новизна 5, `newprove` | [Двумерная рекурсия](verification-graph/coverage.md#node-newprove) | Доказаны биномиальные подсчёты в `Nat.choose`, обе точные вещественные плотности и двусторонняя оценка `4^N/(2N+1) ≤ length(T(N,N)) ≤ 4^N`. Центральная биномиальная асимптотика и диагональный логарифмический предел выведены из формулы Стирлинга mathlib |
| Минимальное число полных разрезов полимино, случай прямоугольника | Новизна 5, `thm:min-dissection-path` | [Разрезы](verification-graph/coverage.md#node-thm-min-dissection-path) | Формула доказана при связности по сторонам и при связной внутренности объединения. Во втором случае пересечение пути с линией обосновано теоремой о промежуточном значении для координаты. Для произвольного объединения дан точный критерий достаточности внутренних линий. При касании двух квадратов только углами имеем λ = 0 и геометрический минимум 1 |
| Компактность и липшицевы оценки для символьно-решёточной метрики | Новизна 5, `propositionn1`, `prop:dSLshift` | [Метрика](verification-graph/coverage.md#node-propositionn1) · [Сдвиг](verification-graph/coverage.md#node-prop-dslshift) | Доказаны метрические свойства, обе оценки на конечных окнах, совпадение с топологией произведения, компактность и полнота замкнутого подсдвига, липшицевы оценки для отображения в банахово пространство и двустороннего сдвига |
| Ряд Миллина, конечное тождество и оценка остатка | Новизна 5, `thm:millin` | [Ряд](verification-graph/coverage.md#node-thm-millin) | Доказаны дробное тождество, формула частичной суммы, равенство для сходящегося ряда и явная оценка остатка `φ⁻ᴹ` при `M = m·2^(N+1)`, из которой следует записанная в TeX оценка `IsBigO` |
| Симметрия конечных сумм и тождество для ряда с чётным сдвигом | Новизна 5, `prop:symm`, `prop:sum2r` | [Симметрия](verification-graph/coverage.md#node-prop-symm) · [Чётный сдвиг](verification-graph/coverage.md#node-prop-sum2r) | Доказаны тождество д’Оканя по Бине, симметрия конечных сумм, сходимость и равенство для ряда с чётным сдвигом |
| Полная факторная и арифметическая сложность конкатенации факториалов | Новизна 6, защита 4, §2.2 | [Сложности](verification-graph/coverage.md#node-mainthm01) | Доказаны `lem:logfact`, `lem:lead`, `lem:trail` и обе формулы сложности `mainthm01` для бесконечного слова над `Fin b`. Для `lem:trail` проверены минимум по показателям простых и оценка Лежандра из доказательства. Доказательство равномерного распределения использует корреляции, сравнение суммы с интегралом, оба предельных перехода и формализованный критерий Вейля |
| Квазиэксперимент, нескорректированные и скорректированные результаты | Новизна 7, §4.3 | [Вывод исследования](verification-graph/coverage.md#node-study-summary) | Для любых парных оценок 42 учеников каждой группы, согласующихся с округлёнными сводками, доказаны оба исходных преимущества B, значимость итогового различия только по тесту на числа до поправки и отсутствие значимости по обоим тестам после ANCOVA. Разности средних приростов по модулю не превосходят 0,06 и 0,54 балла. Точность исходных наблюдений, ранговые тесты и диагностика модели остаются открытыми |

## Положения, выносимые на защиту

| Положение в TeX | Итоговые теоремы Lean |
|---|---|
| 1. Скрученные повторы и динамика | [`wordOnCycle_twisted_critical_exponent`, `wordOnCycle_periodic_case`, `wordOnCycle_binary_avoidance`](Thesis/ThueMorseCyclicAlphabet.lean), [`finiteWord_dynamics`](Thesis/ThueMorseDynamics.lean) |
| 2. Богатство и палиндромная плотность | [`rich_factor_infiniteWord`](Thesis/TernaryRichness.lean), [`palindromicDensity_insert`](Thesis/PalindromicDensityReal.lean), [`characteristic_palindromicDensity_gt_half_iff`, границы, спектральный разрыв и постоянный хвост](Thesis/SturmianPalindromicDensity.lean), [`standardWord_palindromicDensity`](Thesis/MBonacciPalindromicDensity.lean) |
| 3. Индексы дерева факторов | [`characteristic_factorGraph_indices`](Thesis/FactorTreeGraphIndices.lean) |
| 4. Факторная и арифметическая сложность слова факториалов | [`infiniteWord_full_complexities`](Thesis/FactorialInfiniteWord.lean) |

Команда `#print axioms` для этих теорем выводит только стандартные аксиомы Lean `propext`, `Quot.sound` и, где используется классическая логика, `Classical.choice`.

## Файлы Lean

- [ThueMorse.lean](Thesis/ThueMorse.lean) — неподвижная точка, периодический случай и бинарный критерий.
- [ThueMorseCyclicAlphabet.lean](Thesis/ThueMorseCyclicAlphabet.lean) — подстановка на исходном алфавите, блочное определение повтора, перенос классификации на целые степени циклической перестановки.
- [ThueMorseCarries.lean](Thesis/ThueMorseCarries.lean) — разности сумм цифр, показатели делимости и формулы переносов из леммы 3.8.4.
- [ThueMorseBinaryCarries.lean](Thesis/ThueMorseBinaryCarries.lean) — выделение чётных индексов окна и ограничение на нечётную длину блока из лемм 3.8.1–3.8.3.
- [ThueMorseClassification.lean](Thesis/ThueMorseClassification.lean) — критерий существования сильного скрученного повтора для произвольного основания в непериодическом случае.
- [ThueMorseBlocks.lean](Thesis/ThueMorseBlocks.lean) — разбиение на блоки и диапазон суммы цифр.
- [ThueMorseRecurrence.lean](Thesis/ThueMorseRecurrence.lean) — граница промежутков 2b^T и исключение финального периода.
- [ThueMorseSubstitution.lean](Thesis/ThueMorseSubstitution.lean) — неподвижная точка и точный порог примитивности.
- [ThueMorseComplexity.lean](Thesis/ThueMorseComplexity.lean) — язык факторов, оценки сложности и скорость логарифмического роста.
- [WordOrbitClosure.lean](Thesis/WordOrbitClosure.lean) — язык одностороннего замыкания орбиты, инвариантность и минимальность.
- [ThueMorseEntropy.lean](Thesis/ThueMorseEntropy.lean) — покрытия цилиндрами и нулевая топологическая энтропия.
- [ThueMorseFourier.lean](Thesis/ThueMorseFourier.lean) — сумма по корням из единицы и строгая граница нетривиальных гармоник.
- [ThueMorseFrequency.lean](Thesis/ThueMorseFrequency.lean) — оценка на полном блоке, краевые ошибки и равномерный предел частот букв.
- [ThueMorseSubshift.lean](Thesis/ThueMorseSubshift.lean) — перенос частот букв и свободы от длинных скрученных повторов на замыкание орбиты.
- [ThueMorseErgodicity.lean](Thesis/ThueMorseErgodicity.lean) — определения инвариантной меры, строгой эргодичности и равномерных частот.
- [OrbitAverageLimits.lean](Thesis/OrbitAverageLimits.lean) и [UniqueErgodicAverages.lean](Thesis/UniqueErgodicAverages.lean) — инвариантные пределы орбитальных средних и равномерная сходимость при единственности меры.
- [WordInvariantMeasures.lean](Thesis/WordInvariantMeasures.lean) — построение инвариантной меры на одностороннем замыкании орбиты.
- [WordUniformFrequencies.lean](Thesis/WordUniformFrequencies.lean) и [WordCylinderMeasures.lean](Thesis/WordCylinderMeasures.lean) — эквивалентность единственности меры и равномерности частот факторов, применение теоремы Мишеля в форме утверждения о единственности меры.
- [ConstantLengthBlocks.lean](Thesis/ConstantLengthBlocks.lean) — выровненное разбиение неподвижного слова и композиция блоков итераций.
- [PrimitiveSubstitutionAverages.lean](Thesis/PrimitiveSubstitutionAverages.lean) — сжатие диапазона средних при примитивности подстановки.
- [AlignedWindowAverages.lean](Thesis/AlignedWindowAverages.lean) и [PrimitiveFactorCenters.lean](Thesis/PrimitiveFactorCenters.lean) — переход от выровненных блоков к произвольным окнам и оценка граничных вхождений факторов.
- [PrimitiveSubstitutionErgodicity.lean](Thesis/PrimitiveSubstitutionErgodicity.lean) — доказательство нужного случая теоремы Мишеля и вывод строгой эргодичности для обобщённого слова Туэ–Морса.
- [ThueMorseDynamics.lean](Thesis/ThueMorseDynamics.lean) — все пять пунктов теоремы `thm:dynWb`.
- [Palindrome.lean](Thesis/Palindrome.lean) — соответствие длин палиндромных префиксов при вставке.
- [PalindromeFactors.lean](Thesis/PalindromeFactors.lean) — классификация и подсчёт факторов при вставке разделителя, верхняя граница числа палиндромных факторов и наследование богатства.
- [TernaryWord.lean](Thesis/TernaryWord.lean) — рекурсия трёхбуквенного слова и вывод богатства из богатства конечных слов Фибоначчи.
- [PalindromicMorphisms.lean](Thesis/PalindromicMorphisms.lean) и [PalindromicMorphismRichness.lean](Thesis/PalindromicMorphismRichness.lean) — подсчёт палиндромов при морфизме и сохранение богатства.
- [GeneralizedFibonacciSeries.lean](Thesis/GeneralizedFibonacciSeries.lean) — исправленные начальные условия и формальная производящая функция по коэффициентам.
- [FibonacciMechanical.lean](Thesis/FibonacciMechanical.lean) — механическое представление слова Фибоначчи, телескопический подсчёт и сбалансированность каждого фактора, предельные плотности букв и оптимальные границы отклонений в префиксах.
- [FibonacciBeatty.lean](Thesis/FibonacciBeatty.lean) — позиции обеих букв по Битти, промежутки между единицами и классификация факторов длины три.
- [FibonacciRichness.lean](Thesis/FibonacciRichness.lean) — богатство конечных слов Фибоначчи.
- [FibonacciCompletePrefixes.lean](Thesis/FibonacciCompletePrefixes.lean) — отождествление рекурсивного слова Фибоначчи с бинарным стандартным эпиштурмовым словом и полный список палиндромных префиксов.
- [FibonacciPalindromeDensity.lean](Thesis/FibonacciPalindromeDensity.lean) — плотность слова Фибоначчи из полного списка и перенос длин и плотности на трёхбуквенное слово.
- [FischlerBound.lean](Thesis/FischlerBound.lean) — общая оценка Фишлера через периоды перекрывающихся палиндромных префиксов. Из неё следуют верхние границы для слова Фибоначчи и для характеристических штурмовых слов.
- [FibonacciCentralPrefixes.lean](Thesis/FibonacciCentralPrefixes.lean) — доказательство леммы о центральных палиндромах по двум разложениям из TeX.
- [WordPrefixLimits.lean](Thesis/WordPrefixLimits.lean) и [TernaryRichness.lean](Thesis/TernaryRichness.lean) — предел вложенных конечных слов и богатство каждого фактора бесконечного трёхбуквенного слова.
- [PalindromeDensity.lean](Thesis/PalindromeDensity.lean) — инвариантность палиндромной плотности.
- [SturmianDensityDichotomy.lean](Thesis/SturmianDensityDichotomy.lean) — обратные цепные дроби, обе части дихотомии и нижняя граница по формуле Фишлера.
- [SturmianConstantTail.lean](Thesis/SturmianConstantTail.lean) — постоянный хвост цепной дроби, явные значения и их монотонность.
- [SturmianDiophantine.lean](Thesis/SturmianDiophantine.lean) — отношения континуантов, оценки ошибки подходящих дробей и критерий плохой приближаемости.
- [PalindromePrefixBlocks.lean](Thesis/PalindromePrefixBlocks.lean) и [SturmianPrefixRatios.lean](Thesis/SturmianPrefixRatios.lean) — вывод формулы Фишлера из блоков длин и идентификация знаменателей с континуантами.
- [SturmianPalindromeRecords.lean](Thesis/SturmianPalindromeRecords.lean), [RotationRecordBrackets.lean](Thesis/RotationRecordBrackets.lean) и [RotationRecordEnumeration.lean](Thesis/RotationRecordEnumeration.lean) — критерий палиндромности и точное перечисление рекордов дробных частей иррационального поворота.
- [SturmianConvergentErrors.lean](Thesis/SturmianConvergentErrors.lean) — чередование знаков и рекурсия погрешностей подходящих дробей.
- [SturmianSemiconvergentRecords.lean](Thesis/SturmianSemiconvergentRecords.lean) — отождествление рекордов с блоками континуантов и доказательство формулы Фишлера и диофантова критерия для механического слова.
- [SturmianWordDensityConsequences.lean](Thesis/SturmianWordDensityConsequences.lean) — явные значения для постоянного хвоста, эффект вставки и теоретико-мерные следствия для самого слова с предпосылками Хинчина и Ярника.
- [SturmianDensitySpectrum.lean](Thesis/SturmianDensitySpectrum.lean) — спектральный разрыв для штурмовых слов, верхняя граница и условие её достижения.
- [BadlyApproximableNull.lean](Thesis/BadlyApproximableNull.lean) — нулевая мера множества плохо приближаемых наклонов и наклонов с ограниченными неполными частными, по теореме Лебега о плотности.
- [BadlyApproximableDimension.lean](Thesis/BadlyApproximableDimension.lean) — нужное утверждение Ярника о размерности 1, через вложенные интервалы, исключение рациональных приближений по диапазонам знаменателей и гёльдерову сюръекцию на отрезок.
- [SturmianNullConsequences.lean](Thesis/SturmianNullConsequences.lean) — нулевая мера исключительного множества и палиндромная плотность 1/2 почти всюду.
- [SturmianPalindromicDensity.lean](Thesis/SturmianPalindromicDensity.lean) — формула Фишлера, дихотомия, точные значения и теоретико-мерные следствия для вещественной плотности характеристических слов.
- [SturmianMetricConsequences.lean](Thesis/SturmianMetricConsequences.lean) — нулевая мера и хаусдорфова размерность 1 исключительных наклонов как в `cor:palSturm` (3).
- [SturmianDensityMeasure.lean](Thesis/SturmianDensityMeasure.lean) — исключительное множество и теоретико-мерные выводы из результатов Хинчина и Ярника.
- [MBonacciDensity.lean](Thesis/MBonacciDensity.lean) — направляющее слово, характеристический многочлен, предел корней и вывод плотности из предела отношений длин префиксов.
- [MBonacciCharacteristic.lean](Thesis/MBonacciCharacteristic.lean) — характеристический многочлен длин, простота доминирующего корня и оценка остальных корней.
- [RecurrenceStability.lean](Thesis/RecurrenceStability.lean) — сходимость при разностном уравнении с корнем модуля меньше единицы.
- [PolynomialRecurrence.lean](Thesis/PolynomialRecurrence.lean) — переход от факторизации характеристического многочлена к коэффициенту доминирующей экспоненты.
- [MBonacciPrefixLimit.lean](Thesis/MBonacciPrefixLimit.lean) — рост разностей, положительный доминирующий коэффициент и предел отношений длин.
- [PalindromicDensityReal.lean](Thesis/PalindromicDensityReal.lean) — вещественная плотность как обратная к верхнему пределу отношений длин для любой возрастающей нумерации палиндромных префиксов. Доказаны принадлежность отрезку [0,1], совместимость с рациональными сечениями и инвариантность вставки.
- [PalPrefixRatio.lean](Thesis/PalPrefixRatio.lean) — строгое рациональное сечение плотности через предел или верхний предел отношений длин.
- [MBonacciWordDensity.lean](Thesis/MBonacciWordDensity.lean) — вывод плотности 1/βₘ из перечисления префиксов и цитируемой рекурсии.
- [PalindromicClosure.lean](Thesis/PalindromicClosure.lean) — кратчайшее палиндромное замыкание и его длина через наибольший палиндромный суффикс.
- [EpisturmianPrefixes.lean](Thesis/EpisturmianPrefixes.lean) и [EpisturmianRecurrence.lean](Thesis/EpisturmianRecurrence.lean) — перечисление палиндромных префиксов и рекурсия по предыдущему вхождению директивной буквы.
- [MBonacciPalindromicDensity.lean](Thesis/MBonacciPalindromicDensity.lean) — вещественная плотность стандартных m-боначчи слов, числовые примеры и убывание к 1/2.
- [MBonacciClosureDensity.lean](Thesis/MBonacciClosureDensity.lean) — плотность стандартного m-боначчи слова с циклической директивой.
- [MBonacciValues.lean](Thesis/MBonacciValues.lean) — рациональные границы корней и проверка округлений плотностей при m=3 и m=4.
- [FactorTree.lean](Thesis/FactorTree.lean) — подсчёт вершин и рёбер и формулы индексов при структурных предпосылках.
- [FactorTreeSpecial.lean](Thesis/FactorTreeSpecial.lean) — единственный правый специальный фактор, степени, специальные рёбра и рёбра из специальных вершин.
- [FactorTreeZagreb.lean](Thesis/FactorTreeZagreb.lean) — явные множества вершин и рёбер и первый индекс Загреба.
- [FactorTreeIncidence.lean](Thesis/FactorTreeIncidence.lean) — подсчёт инцидентностей листьев и вершин степени три.
- [FactorTreeEdgeCounts.lean](Thesis/FactorTreeEdgeCounts.lean) — пары степеней на фактических рёбрах, подсчёт рёбер между специальными вершинами и от специальных вершин к листьям.
- [FactorTreeMixedEdges.lean](Thesis/FactorTreeMixedEdges.lean) — раздельные подсчёты входящих и исходящих смешанных рёбер и полная классификация рёбер по степеням.
- [FactorTreeIndices.lean](Thesis/FactorTreeIndices.lean) — формулы числа вершин и всех четырёх индексов дерева факторов при F1 и F2.
- [FactorTreeGraph.lean](Thesis/FactorTreeGraph.lean) — граф с рёбрами по дописыванию одной буквы, связность, число рёбер и свойство дерева.
- [TreeIrregularity.lean](Thesis/TreeIrregularity.lean) — оценки квадратичного индекса на рёбрах, формула для звезды и строгая максимальность по исправленному предложению.
- [TreeIrregularityLower.lean](Thesis/TreeIrregularityLower.lean) — нижняя оценка по рёберно непересекающимся путям к листьям и полный критерий равенства.
- [TreeIrregularityPath.lean](Thesis/TreeIrregularityPath.lean) — значение квадратичного индекса у пути и строгая нижняя оценка для остальных деревьев.
- [FactorTreeGraphIndices.lean](Thesis/FactorTreeGraphIndices.lean) — перенос четырёх формул индексов на степени вершин `SimpleGraph`.
- [FactorTreeDegrees.lean](Thesis/FactorTreeDegrees.lean) — степень вершины как мощность множества инцидентных рёбер.
- [FactorTreeTable.lean](Thesis/FactorTreeTable.lean) — проверка всех четырёх строк таблицы для глубины 8.
- [SturmianMechanical.lean](Thesis/SturmianMechanical.lean) — механическое определение характеристического слова, его апериодичность и описание правых специальных факторов обращением префиксов.
- [SturmianRichness.lean](Thesis/SturmianRichness.lean), [SturmianFactorRichness.lean](Thesis/SturmianFactorRichness.lean) и [InfiniteRichness.lean](Thesis/InfiniteRichness.lean) — доказательство цитируемого результата о богатстве факторов штурмовых слов и следствие о вставке разделителя.
- [SturmianFactorTree.lean](Thesis/SturmianFactorTree.lean) — сложность k+1 и теорема о числе вершин и индексах для характеристического слова иррационального наклона.
- [SturmianFactorTreeExamples.lean](Thesis/SturmianFactorTreeExamples.lean) — частный случай слова Фибоначчи и явные иррациональные наклоны для всех строк таблицы.
- [SymbolicLatticeMetric.lean](Thesis/SymbolicLatticeMetric.lean) и [SymbolicLatticeTopology.lean](Thesis/SymbolicLatticeTopology.lean) — метрика, оценки на конечных окнах, компактность и липшицевость.
- [PolyominoPieces.lean](Thesis/PolyominoPieces.lean) и [PolyominoGeometry.lean](Thesis/PolyominoGeometry.lean) — пути через общие стороны, компоненты остатка после удаления прямых, геометрический минимум и контрпример при касании в углу.
- [PolyominoInterior.lean](Thesis/PolyominoInterior.lean) и [PolyominoContacts.lean](Thesis/PolyominoContacts.lean) — пересечение внутренних рёбер при связной внутренности, критерий достаточности разрезов для любых контактов и точный минимум в контрпримере.
- [Polyomino.lean](Thesis/Polyomino.lean) — минимум полных разрезов и формула для прямоугольника.
- [LatticeWord.lean](Thesis/LatticeWord.lean) — биномиальные подсчёты, точные плотности и двусторонняя оценка диагонального роста.
- [LatticeWordStirling.lean](Thesis/LatticeWordStirling.lean) — центральная биномиальная асимптотика и логарифмический предел по формуле Стирлинга mathlib.
- [Fibonacci.lean](Thesis/Fibonacci.lean) — подсчёты в обрамлённых словах и проверка конечных строк таблицы.
- [FramedFibonacciDensity.lean](Thesis/FramedFibonacciDensity.lean) — точная формула погрешности для обрамлённых слов после умножения на знаменатели.
- [FibonacciTableLimit.lean](Thesis/FibonacciTableLimit.lean) — точная ошибка необрамлённых слов, оценка по Бине и проверка округлений предельной строки.
- [FibonacciBinet.lean](Thesis/FibonacciBinet.lean) — вывод тождества д’Оканя, формулы и оценки плотностей из формулы Бине.
- [FibonacciSeries.lean](Thesis/FibonacciSeries.lean) и [FibonacciGoldenLimits.lean](Thesis/FibonacciGoldenLimits.lean) — остатки по формуле Бине, точные плотности и пределы при золотом сечении, сходимость и значения двух рядов.
- [FibonacciTelescoping.lean](Thesis/FibonacciTelescoping.lean) — симметрия конечных сумм и телескопирование в формулах для чётного сдвига и ряда Миллина.
- [FibonacciIdentities.lean](Thesis/FibonacciIdentities.lean) — тождества д’Оканя, Кассини и шаг телескопирования для ряда Миллина.
- [FactorialLogarithms.lean](Thesis/FactorialLogarithms.lean) — критерий дробной части логарифма и переход от распределения к обеим формулам сложности.
- [FactorialCorrelations.lean](Thesis/FactorialCorrelations.lean) — корреляционное тождество, оценка ошибки и условный предел модуля.
- [LogOscillationIntegral.lean](Thesis/LogOscillationIntegral.lean) — первообразная, точная оценка ошибки сравнения суммы с интегралом и нормированный остаток.
- [VanDerCorput.lean](Thesis/VanDerCorput.lean) и [VanDerCorputLimit.lean](Thesis/VanDerCorputLimit.lean) — продолжение нулями, раскрытие квадрата, переход к пределу при фиксированном размере окна и гармоническая оценка.
- [WeylCriterion.lean](Thesis/WeylCriterion.lean) — используемое направление критерия Вейля через плотность тригонометрических многочленов.
- [FactorialWeyl.lean](Thesis/FactorialWeyl.lean) — экспоненциальные средние, равномерное распределение, бесконечные попадания в интервалы и обе формулы сложности.
- [FactorialLeadingDigits.lean](Thesis/FactorialLeadingDigits.lean) — арифметический переход от интервального условия к заданным начальным цифрам.
- [FactorialInfiniteWord.lean](Thesis/FactorialInfiniteWord.lean) — бесконечная конкатенация и полный подсчёт факторов и арифметических факторов.
- [FactorialWord.lean](Thesis/FactorialWord.lean) — точное число конечных нулей в записи факториала по показателям простых, конечные префиксы и подсчёты при условии леммы о начальных цифрах.

- [StudyANCOVA.lean](Thesis/StudyANCOVA.lean) — модель ANCOVA из §4.3, связь попарных приростов с ковариацией, оценка коэффициента группы, остаточной суммы квадратов и множителя его дисперсии.
- [StudyANCOVATable.lean](Thesis/StudyANCOVATable.lean) — проверка интервалов для скорректированных разностей, статистик ANCOVA и Уэлча по опубликованным сводным данным при округлении до сотых.
- [StudentTails.lean](Thesis/StudentTails.lean) и [StudyReferenceBounds.lean](Thesis/StudyReferenceBounds.lean) — интегральное определение двусторонней вероятности Стьюдента и доказанные границы при уровне 0,05 и вещественных степенях свободы от 80 до 82.
- [StudySignificance.lean](Thesis/StudySignificance.lean) — выводы тестов Уэлча и ANCOVA из округлённых сводок и их связь с регрессией по индивидуальным парным наблюдениям.

## Сборка

Из папки `lean-verification/` с установленным [Elan](https://github.com/leanprover/elan). Версия mathlib закреплена в `lake-manifest.json`. При доступе к серверу кэша команда `lake exe cache get` перед сборкой ускоряет первую сборку.

```sh
lake build
```
