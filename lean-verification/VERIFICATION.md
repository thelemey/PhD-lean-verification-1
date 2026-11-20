# Формальная верификация диссертации

За основу взяты разделы «Научная новизна работы» и «Положения, выносимые на защиту» из [исправленного TeX](../corrected_thesis/thesis_corrected.tex). [Граф зависимостей](../dependency_graph_bundle/dependency_graph.json) относится к представленной редакции и служит указателем к доказательствам и замечаниям. Статус `novelty` в графе присвоен замечаниям N1–N3 о новизне или статусе результата. Пометка «защита» ниже относится к нумерации во введении исправленного TeX.

| Утверждение | Источник | Граф | Статус Lean |
|---|---|---|---|
| Неподвижная точка обобщённой подстановки, классификация сильных скрученных повторов, бинарное следствие | Новизна 1, защита 1, §3.8, `tw:main`, `avoidance` | D0–D4, E5 | Доказаны формула суммы цифр, периодический и непериодический случаи классификации и бинарный критерий для кубов |
| Минимальность, нулевая энтропия, строгая эргодичность | Новизна 1, защита 1, `thm:dynWb` | D5–D8 | Доказаны разбиение на выровненные блоки, примитивность с порогом N−1, неподвижность слова, равномерная рекуррентность и отсутствие финального периода в заявленном случае. Для одностороннего замыкания орбиты доказаны минимальность, обе оценки сложности при положительной длине и нулевая топологическая энтропия в определении mathlib. Проверены фильтр корней из единицы, оценка ошибки на произвольном окне и равномерная частота 1/N каждой буквы по всему замыканию орбиты. Доказано равенство языков факторов. Выведено следствие об отсутствии длинных скрученных повторов. Построена инвариантная вероятностная мера. Доказаны эквивалентность её единственности и равномерности частот всех факторов и используемый случай теоремы Мишеля для примитивных подстановок постоянной длины. Все пять пунктов, включая строгую эргодичность, объединены в `finiteWord_dynamics` |
| Формулы индексов дерева факторов и число вершин | Новизна 2, защита 3, `thm:factortree` | G0–G3 | Для дерева факторов доказаны число вершин, все пять подсчётов по парам степеней, оба индекса Альбертсона и оба индекса Загреба. Проверены четыре строки таблицы для глубины 8 и построены характеристические слова, реализующие каждую строку. Доказан частный случай слова Фибоначчи. Свойства F1 (сложность k+1) и F2 (обращение префикса) доказаны из механического определения характеристического слова. Итоговая теорема использует исходные условия о наклоне, начальной серии и глубине |
| Точная погрешность плотности в обрамлённых словах и числовая таблица | Новизна 3, §3.5, `thm1Asymptotic` | B4–B7 | Доказаны формулы длины и числа букв, точные ошибки по Бине, односторонность обрамлённого случая и чередование знака необрамлённого, оценки скоростей и пределы плотностей. Проверены шесть конечных строк таблицы и округления всех четырёх столбцов предельной строки |
| Богатство факторов трёхбуквенного слова | Новизна 4, защита 2, `thm:Yrich` | C4–C7 | Доказано классическое богатство конечных слов Фибоначчи. По лемме о вставке разделителя и наследованию богатства доказаны точный подсчёт для всех конечных слов и богатство каждого фактора бесконечного трёхбуквенного слова |
| Инвариантность палиндромной плотности при вставке разделителя | Новизна 4, защита 2, `prop:insertion` | C8–C9 | Доказано совпадение строгих рациональных нижних сечений плотности, включая случай конечного числа префиксов |
| Дихотомия палиндромной плотности, явные значения и диофантовы и теоретико-мерные следствия | Новизна 4, защита 2, `prop:dichotomy`, `cor:palSturm` | C2, C10–C12 | На уровне формулы Фишлера для характеристических штурмовых слов доказаны дихотомия, диофантов критерий, обе границы плотности, спектральный разрыв и точное условие для максимума. Формула Фишлера выведена из классического перечисления по блокам длин; отдельно доказано точное перечисление палиндромных префиксов механического слова через рекорды дробных частей. Для критерия по наклону остаётся отождествить эти рекорды с блоками континуантов. Связь с инвариантностью при вставке разделителя проверена. Множество исключительных наклонов отождествлено с множеством плохо приближаемых чисел на (0,1). Почти всюду плотность равна 1/2 при условии результата Хинчина. Вывод о нулевой мере и хаусдорфовой размерности 1 использует результаты Хинчина и Ярника как явные предпосылки |
| Палиндромная плотность m-боначчи слов | Новизна 4, защита 2, `prop:mbonacci` | C2, C12 | Из цитируемой рекурсии Фишлера для перечисления палиндромных префиксов доказаны рост разностей, положительность коэффициента при βₘⁱ, предел отношений длин βₘ и плотность 1/βₘ. Доказано убывание этих плотностей до 1/2. Проверены значение 1/φ при m=2 и рациональные границы для численных примеров, включая округления плотностей 0,5437 и 0,5188. Для β₄ строго доказано 1,92756 < β₄ < 1,92757, так что 1,9276 в исходнике представляет округление. Для самого стандартного слова с циклической директивой из палиндромных замыканий доказано, что их длины исчерпывают все палиндромные префиксы. Из предыдущего вхождения директивной буквы получена нужная рекурсия и доказана плотность 1/βₘ |
| Биномиальные подсчёты, точные плотности, логарифмический предел | Новизна 5, `newprove` | — | Доказаны биномиальные подсчёты, обе точные плотности и двусторонняя оценка `4^N/(2N+1) ≤ length(T(N,N)) ≤ 4^N`. Центральная биномиальная асимптотика и диагональный логарифмический предел выведены из формулы Стирлинга mathlib |
| Минимальное число полных разрезов полимино, случай прямоугольника | Новизна 5, `thm:min-dissection-path` | Q0–Q1 | Доказано, включая случай прямоугольника |
| Компактность и липшицевы оценки для символьно-решёточной метрики | Новизна 5, `propositionn1`, `prop:dSLshift` | N3, M1 | Доказаны метрические свойства, обе оценки на конечных окнах, совпадение с топологией произведения, компактность и полнота замкнутого подсдвига, липшицевы оценки для отображения в банахово пространство и двустороннего сдвига |
| Ряд Миллина, конечное тождество и оценка остатка | Новизна 5, `thm:millin` | — | Доказаны дробное тождество, формула частичной суммы, её предел и явная оценка остатка `φ⁻ᴹ` при `M = m·2^(N+1)` |
| Симметрия конечных сумм и тождество для ряда с чётным сдвигом | Новизна 5, `prop:symm`, `prop:sum2r` | — | Доказаны тождество д’Оканя по Бине, симметрия конечных сумм и формула ряда с чётным сдвигом в виде предела частичных сумм |
| Полная факторная и арифметическая сложность конкатенации факториалов | Новизна 6, защита 4, §2.2 | F1–F5 | Доказаны `lem:logfact`, `lem:lead`, `lem:trail` и обе формулы сложности `mainthm01`. Доказательство равномерного распределения использует корреляции, сравнение суммы с интегралом, оба предельных перехода и формализованный критерий Вейля |
| Квазиэксперимент, нескорректированные и скорректированные результаты | Новизна 7, §4.3 | — | Эмпирическая часть. Для проверки расчётов нужны исходные данные или достаточные сводные статистики и спецификация модели |

## Файлы Lean

- [ThueMorse.lean](Thesis/ThueMorse.lean) — неподвижная точка, периодический случай и бинарный критерий.
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
- [FibonacciRichness.lean](Thesis/FibonacciRichness.lean) — богатство конечных слов Фибоначчи.
- [FibonacciCentralPrefixes.lean](Thesis/FibonacciCentralPrefixes.lean) — доказательство леммы о центральных палиндромах по двум разложениям из TeX.
- [WordPrefixLimits.lean](Thesis/WordPrefixLimits.lean) и [TernaryRichness.lean](Thesis/TernaryRichness.lean) — предел вложенных конечных слов и богатство каждого фактора бесконечного трёхбуквенного слова.
- [PalindromeDensity.lean](Thesis/PalindromeDensity.lean) — инвариантность палиндромной плотности.
- [SturmianDensityDichotomy.lean](Thesis/SturmianDensityDichotomy.lean) — обратные цепные дроби, обе части дихотомии и нижняя граница по формуле Фишлера.
- [SturmianConstantTail.lean](Thesis/SturmianConstantTail.lean) — постоянный хвост цепной дроби, явные значения и их монотонность.
- [SturmianDiophantine.lean](Thesis/SturmianDiophantine.lean) — отношения континуантов, оценки ошибки подходящих дробей и критерий плохой приближаемости.
- [PalindromePrefixBlocks.lean](Thesis/PalindromePrefixBlocks.lean) и [SturmianPrefixRatios.lean](Thesis/SturmianPrefixRatios.lean) — вывод формулы Фишлера из блоков длин и идентификация знаменателей с континуантами.
- [SturmianPalindromeRecords.lean](Thesis/SturmianPalindromeRecords.lean), [RotationRecordBrackets.lean](Thesis/RotationRecordBrackets.lean) и [RotationRecordEnumeration.lean](Thesis/RotationRecordEnumeration.lean) — критерий палиндромности и точное перечисление рекордов дробных частей иррационального поворота.
- [SturmianDensitySpectrum.lean](Thesis/SturmianDensitySpectrum.lean) — спектральный разрыв для штурмовых слов, верхняя граница и условие её достижения.
- [SturmianDensityMeasure.lean](Thesis/SturmianDensityMeasure.lean) — исключительное множество и теоретико-мерные выводы из результатов Хинчина и Ярника.
- [MBonacciDensity.lean](Thesis/MBonacciDensity.lean) — направляющее слово, характеристический многочлен, предел корней и вывод плотности из предела отношений длин префиксов.
- [MBonacciCharacteristic.lean](Thesis/MBonacciCharacteristic.lean) — характеристический многочлен длин, простота доминирующего корня и оценка остальных корней.
- [RecurrenceStability.lean](Thesis/RecurrenceStability.lean) — сходимость при разностном уравнении с корнем модуля меньше единицы.
- [PolynomialRecurrence.lean](Thesis/PolynomialRecurrence.lean) — переход от факторизации характеристического многочлена к коэффициенту доминирующей экспоненты.
- [MBonacciPrefixLimit.lean](Thesis/MBonacciPrefixLimit.lean) — рост разностей, положительный доминирующий коэффициент и предел отношений длин.
- [PalPrefixRatio.lean](Thesis/PalPrefixRatio.lean) — строгое рациональное сечение плотности через предел или верхний предел отношений длин.
- [MBonacciWordDensity.lean](Thesis/MBonacciWordDensity.lean) — вывод плотности 1/βₘ из перечисления префиксов и цитируемой рекурсии.
- [PalindromicClosure.lean](Thesis/PalindromicClosure.lean) — кратчайшее палиндромное замыкание и его длина через наибольший палиндромный суффикс.
- [EpisturmianPrefixes.lean](Thesis/EpisturmianPrefixes.lean) и [EpisturmianRecurrence.lean](Thesis/EpisturmianRecurrence.lean) — перечисление палиндромных префиксов и рекурсия по предыдущему вхождению директивной буквы.
- [MBonacciClosureDensity.lean](Thesis/MBonacciClosureDensity.lean) — плотность стандартного m-боначчи слова с циклической директивой.
- [MBonacciValues.lean](Thesis/MBonacciValues.lean) — рациональные границы корней и проверка округлений плотностей при m=3 и m=4.
- [FactorTree.lean](Thesis/FactorTree.lean) — подсчёт вершин и рёбер и формулы индексов при структурных предпосылках.
- [FactorTreeSpecial.lean](Thesis/FactorTreeSpecial.lean) — единственный правый специальный фактор, степени, специальные рёбра и рёбра из специальных вершин.
- [FactorTreeZagreb.lean](Thesis/FactorTreeZagreb.lean) — явные множества вершин и рёбер и первый индекс Загреба.
- [FactorTreeIncidence.lean](Thesis/FactorTreeIncidence.lean) — подсчёт инцидентностей листьев и вершин степени три.
- [FactorTreeEdgeCounts.lean](Thesis/FactorTreeEdgeCounts.lean) — пары степеней на фактических рёбрах, подсчёт рёбер между специальными вершинами и от специальных вершин к листьям.
- [FactorTreeMixedEdges.lean](Thesis/FactorTreeMixedEdges.lean) — раздельные подсчёты входящих и исходящих смешанных рёбер и полная классификация рёбер по степеням.
- [FactorTreeIndices.lean](Thesis/FactorTreeIndices.lean) — формулы числа вершин и всех четырёх индексов дерева факторов при F1 и F2.
- [FactorTreeDegrees.lean](Thesis/FactorTreeDegrees.lean) — степень вершины как мощность множества инцидентных рёбер.
- [FactorTreeTable.lean](Thesis/FactorTreeTable.lean) — проверка всех четырёх строк таблицы для глубины 8.
- [SturmianMechanical.lean](Thesis/SturmianMechanical.lean) — механическое определение характеристического слова, его апериодичность и описание правых специальных факторов обращением префиксов.
- [SturmianFactorTree.lean](Thesis/SturmianFactorTree.lean) — сложность k+1 и теорема о числе вершин и индексах для характеристического слова иррационального наклона.
- [SturmianFactorTreeExamples.lean](Thesis/SturmianFactorTreeExamples.lean) — частный случай слова Фибоначчи и явные иррациональные наклоны для всех строк таблицы.
- [SymbolicLatticeMetric.lean](Thesis/SymbolicLatticeMetric.lean) и [SymbolicLatticeTopology.lean](Thesis/SymbolicLatticeTopology.lean) — метрика, оценки на конечных окнах, компактность и липшицевость.
- [Polyomino.lean](Thesis/Polyomino.lean) — минимум полных разрезов и формула для прямоугольника.
- [LatticeWord.lean](Thesis/LatticeWord.lean) — биномиальные подсчёты, точные плотности и двусторонняя оценка диагонального роста.
- [LatticeWordStirling.lean](Thesis/LatticeWordStirling.lean) — центральная биномиальная асимптотика и логарифмический предел по формуле Стирлинга mathlib.
- [Fibonacci.lean](Thesis/Fibonacci.lean) — подсчёты в обрамлённых словах и проверка конечных строк таблицы.
- [FramedFibonacciDensity.lean](Thesis/FramedFibonacciDensity.lean) — точная формула погрешности для обрамлённых слов после умножения на знаменатели.
- [FibonacciTableLimit.lean](Thesis/FibonacciTableLimit.lean) — точная ошибка необрамлённых слов, оценка по Бине и проверка округлений предельной строки.
- [FibonacciBinet.lean](Thesis/FibonacciBinet.lean) — вывод тождества д’Оканя, формулы и оценки плотностей из формулы Бине.
- [FibonacciSeries.lean](Thesis/FibonacciSeries.lean) и [FibonacciGoldenLimits.lean](Thesis/FibonacciGoldenLimits.lean) — остатки и вещественные пределы по формуле Бине со специализацией к золотому сечению mathlib.
- [FibonacciTelescoping.lean](Thesis/FibonacciTelescoping.lean) — симметрия конечных сумм и телескопирование в формулах для чётного сдвига и ряда Миллина.
- [FibonacciIdentities.lean](Thesis/FibonacciIdentities.lean) — тождества д’Оканя, Кассини и шаг телескопирования для ряда Миллина.
- [FactorialLogarithms.lean](Thesis/FactorialLogarithms.lean) — критерий дробной части логарифма и переход от распределения к обеим формулам сложности.
- [FactorialCorrelations.lean](Thesis/FactorialCorrelations.lean) — корреляционное тождество, оценка ошибки и условный предел модуля.
- [LogOscillationIntegral.lean](Thesis/LogOscillationIntegral.lean) — первообразная, точная оценка ошибки сравнения суммы с интегралом и нормированный остаток.
- [VanDerCorput.lean](Thesis/VanDerCorput.lean) и [VanDerCorputLimit.lean](Thesis/VanDerCorputLimit.lean) — продолжение нулями, раскрытие квадрата, переход к пределу при фиксированном размере окна и гармоническая оценка.
- [WeylCriterion.lean](Thesis/WeylCriterion.lean) — используемое направление критерия Вейля через плотность тригонометрических многочленов.
- [FactorialWeyl.lean](Thesis/FactorialWeyl.lean) — экспоненциальные средние, равномерное распределение, бесконечные попадания в интервалы и обе формулы сложности.
- [FactorialLeadingDigits.lean](Thesis/FactorialLeadingDigits.lean) — арифметический переход от интервального условия к заданным начальным цифрам.
- [FactorialWord.lean](Thesis/FactorialWord.lean) — конечные нули в записи факториала и обе формулы сложности при условии леммы о начальных цифрах.

## Сборка

Из папки `lean-verification/` с установленным [Elan](https://github.com/leanprover/elan). Версия mathlib закреплена в `lake-manifest.json`. При доступе к серверу кэша команда `lake exe cache get` перед сборкой ускоряет первую сборку.

```sh
lake build
```
