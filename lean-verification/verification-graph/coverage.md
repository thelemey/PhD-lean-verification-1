# Узлы графа и доказательства Lean

Метки в квадратных скобках, цвета и стрелки взяты из графа экспертизы представленной редакции. Статус Lean относится к указанным теоремам и их формулировкам в исправленном TeX.

- **Доказано** — утверждение узла покрыто указанными теоремами.
- **С уточнением** — доказана исправленная формулировка либо формулировка с указанным условием.
- **Частично** — в узле есть проверенный результат и непокрытая часть.
- **Определение** — в Lean задан объект, используемый в доказательстве.
- **Без отметки** — для узла в этой карте не указано доказательство Lean.

Полный перечень работ, включая утверждения за пределами исходного графа, приведён в [VERIFICATION.md](../VERIFICATION.md).

## 2.2  Конкатенация факториалов

| Узел | Статус Lean | Покрытие и ссылки |
|---|---|---|
| <a name="node-e1"></a> **E1** Текст перед леммой 2.2.1 | С уточнением | Для любого основания b > 1 доказано равномерное распределение дробных частей log_b(n!), то есть исправленная формулировка. [`factorial_logs_equidistributed`](../Thesis/FactorialWeyl.lean#L49) |
| <a name="node-f1"></a> **F1** Лемма 2.2.1 | Доказано | Доказаны равномерное распределение и попадания в любой полуинтервал положительной длины за любой заданной границей. [`factorial_logs_equidistributed`](../Thesis/FactorialWeyl.lean#L49), [`factorial_logs_hit_interval`](../Thesis/FactorialWeyl.lean#L56) |
| <a name="node-f2"></a> **F2** Лемма 2.2.2 | Доказано | Любой допустимый префикс с ненулевой первой цифрой появляется в сколь угодно поздних факториалах. [`factorial_leading_prefixes`](../Thesis/FactorialWeyl.lean#L63) |
| <a name="node-f3"></a> **F3** Лемма 2.2.3 | Доказано | Проверены точная формула через показатели простых, монотонность и стремление числа концевых нулей к бесконечности. [`factorial_trailingZeroCount_eq_min`](../Thesis/FactorialWord.lean#L150), [`factorial_trailingZeroCount_monotone`](../Thesis/FactorialWord.lean#L181), [`factorial_trailingZeroCount_tendsto_atTop`](../Thesis/FactorialInfiniteWord.lean#L40) |
| <a name="node-f4"></a> **F4** Предл. 2.2.2 | Доказано | Для произвольного слова над конечным алфавитом доказана цепочка p(k) ≤ a(k) ≤ &#124;A&#124;^k через прогрессии шага один и включение в множество всех слов длины k. [`complexity_le_arithmeticLanguage_card_le`](../Thesis/FactorialInfiniteWord.lean#L103) |
| <a name="node-f5"></a> **F5** Теорема 2.2.3 | Доказано | Обе сложности бесконечной конкатенации над Fin b равны b^k. [`infiniteWord_full_complexities`](../Thesis/FactorialInfiniteWord.lean#L147) |

## 3.1  Ошибки предварительного раздела

| Узел | Статус Lean | Покрытие и ссылки |
|---|---|---|
| <a name="node-e2"></a> **E2** Формула (3.4) | Без отметки | — |
| <a name="node-e3"></a> **E3** Определение 3.1.2 | Без отметки | — |
| <a name="node-a1"></a> **A1** Лемма 3.1.1 | Без отметки | — |
| <a name="node-e4"></a> **E4** Теорема 3.1.1 | Без отметки | — |

## 3.4–3.5  Буквы, механическое описание, обрамления

| Узел | Статус Lean | Покрытие и ссылки |
|---|---|---|
| <a name="node-b0"></a> **B0** Рекурсия слова Фибоначчи | Определение | Заданы конечные рекурсивные слова и их бесконечный предел. [`word`](../Thesis/Fibonacci.lean#L13), [`infiniteWord`](../Thesis/FibonacciCentralPrefixes.lean#L92) |
| <a name="node-b1"></a> **B1** Предл. 3.4.1 | Доказано | Доказано равенство рекурсивного слова и характеристического механического слова наклона 1/φ², включая формулу для буквы. Предложение в TeX приведено со ссылкой на Lothaire. [`infiniteWord_eq_mechanicalWord`](../Thesis/FibonacciMechanical.lean#L189), [`infiniteWord_letter_floor`](../Thesis/FibonacciMechanical.lean#L214) |
| <a name="node-b2"></a> **B2** Теорема 3.4.2 | Без отметки | — |
| <a name="node-b3"></a> **B3** Предл. 3.4.3 | Без отметки | — |
| <a name="node-b4"></a> **B4** Леммы 3.5.1 → 3.5.2 | Без отметки | — |
| <a name="node-b5"></a> **B5** Предл. 3.5.3 → 3.5.4 | Доказано | Проверены длины и оба подсчёта букв для исходных и обрамлённых конечных слов. [`word_length`](../Thesis/Fibonacci.lean#L20), [`word_count_a`](../Thesis/Fibonacci.lean#L28), [`word_count_b`](../Thesis/Fibonacci.lean#L36), [`framed_length`](../Thesis/Fibonacci.lean#L43), [`framed_count_a`](../Thesis/Fibonacci.lean#L46), [`framed_count_b`](../Thesis/Fibonacci.lean#L50) |
| <a name="node-b6"></a> **B6** Лемма 3.1.2 | Доказано | Проверены тождества Бине и все три предела отношений из lem:fibA. [`binet`](../Thesis/FibonacciBinet.lean#L13), [`fib_next_sub_phi_mul`](../Thesis/FibonacciBinet.lean#L37), [`previousRatio_binet`](../Thesis/FibonacciBinet.lean#L64), [`golden_fibonacci_ratio_limits`](../Thesis/FibonacciTableLimit.lean#L115) |
| <a name="node-b7"></a> **B7** Теорема 3.5.5 | Доказано | Проверены точные плотности, знак погрешности, пределы и обе скорости из thm1Asymptotic. [`golden_framed_densities_exact`](../Thesis/FibonacciGoldenLimits.lean#L46), [`golden_framed_density_limits`](../Thesis/FibonacciGoldenLimits.lean#L14), [`golden_framed_density_rates`](../Thesis/FibonacciGoldenLimits.lean#L65) |

## 3.6  Палиндромы

| Узел | Статус Lean | Покрытие и ссылки |
|---|---|---|
| <a name="node-c1"></a> **C1** Лемма 3.6.1 | Доказано | Центральные слова палиндромны и дают указанные длины префиксов. Полнота списка относится к C12. [`central_reverse`](../Thesis/FibonacciCentralPrefixes.lean#L50), [`central_length`](../Thesis/FibonacciCentralPrefixes.lean#L64), [`central_palPrefix`](../Thesis/FibonacciCentralPrefixes.lean#L94) |
| <a name="node-c2"></a> **C2** Теорема 3.6.2 (Фишлер) | Без отметки | Узел относится к общей теореме Фишлера для произвольного непериодического слова. В C11 проверена оценка для характеристических штурмовых слов. |
| <a name="node-c3"></a> **C3** Теорема 3.6.3 | С уточнением | Плотность рекурсивного слова Фибоначчи равна 1/φ. Предел отношений рассчитан по полному списку префиксов, приведённому в замечании TeX. Общая оценка Фишлера из C2 отдельно не доказана. [`infiniteWord_palindromicDensity`](../Thesis/FibonacciPalindromeDensity.lean#L47) |
| <a name="node-c4"></a> **C4** Лемма 3.6.2 | С уточнением | Проверены кодирование конечных слов и равенство бесконечных слов. Вложенность начинается с n = 1, а y₀ не является префиксом y₁. [`word_succ_eq_interleave`](../Thesis/TernaryWord.lean#L15), [`word_prefix_succ`](../Thesis/TernaryWord.lean#L22), [`word_zero_not_prefix_one`](../Thesis/TernaryWord.lean#L30), [`infiniteWord_eq_insertSeparator`](../Thesis/TernaryRichness.lean#L39) |
| <a name="node-c5"></a> **C5** Лемма 3.6.3 | Доказано | Получено точное соответствие длин m ↦ 2m+1 и исключены положительные чётные длины. [`palPrefix_insert_iff`](../Thesis/Palindrome.lean#L44), [`not_palPrefix_insert_even`](../Thesis/Palindrome.lean#L36) |
| <a name="node-c6"></a> **C6** Предл. 3.6.7 | Доказано | Доказано равенство вещественных палиндромных плотностей после вставки, включая случай конечного числа префиксов. [`palindromicDensity_insert`](../Thesis/PalindromicDensityReal.lean#L130) |
| <a name="node-c7"></a> **C7** Теорема 3.6.8 | Доказано | Проверены полный список длин 2Fₖ−3 и плотность 1/φ для трёхбуквенного слова по соответствию префиксов и инвариантности при вставке. [`ternary_palPrefix_iff`](../Thesis/FibonacciPalindromeDensity.lean#L57), [`ternary_palindromicDensity`](../Thesis/FibonacciPalindromeDensity.lean#L71) |
| <a name="node-c8"></a> **C8** Лемма 3.6.4 | Доказано | Проверено соответствие палиндромных факторов и формула 2P+1 для числа палиндромов при вставке с двумя граничными разделителями. [`palindromicFactor_framed_iff`](../Thesis/PalindromeFactors.lean#L198), [`framed_factor_count`](../Thesis/PalindromeFactors.lean#L349) |
| <a name="node-c9"></a> **C9** Теорема 3.6.10 | Доказано | Доказано богатство каждого конечного yₙ и всех факторов бесконечного y. [`rich_word`](../Thesis/TernaryRichness.lean#L11), [`palindromic_factor_count`](../Thesis/TernaryRichness.lean#L14), [`rich_factor_infiniteWord`](../Thesis/TernaryRichness.lean#L89) |
| <a name="node-c10"></a> **C10** Теоремы 3.6.12 → 3.6.13 | Доказано | Проверены полный список положительных длин по континуантам, включая два начальных блока, и формула Фишлера для характеристического слова. [`characteristic_palPrefix_iff_full_continuant_blocks`](../Thesis/SturmianSemiconvergentRecords.lean#L317), [`fullPrefixDenominator_step`](../Thesis/SturmianSemiconvergentRecords.lean#L303), [`characteristic_palindromicDensity`](../Thesis/SturmianPalindromicDensity.lean#L9) |
| <a name="node-c11"></a> **C11** Предл. 3.6.14; след. 3.6.15 | Доказано | Проверены дихотомия, обе границы, критерий максимума, постоянный хвост, эффект вставки и теоретико-мерные следствия. [`characteristic_palindromicDensity_bounded`](../Thesis/SturmianPalindromicDensity.lean#L21), [`characteristic_palindromicDensity_unbounded`](../Thesis/SturmianPalindromicDensity.lean#L16), [`characteristic_palindromicDensity_gt_half_iff`](../Thesis/SturmianPalindromicDensity.lean#L28), [`characteristic_palindromicDensity_bounds`](../Thesis/SturmianPalindromicDensity.lean#L35), [`characteristic_palindromicDensity_ae_eq_half`](../Thesis/SturmianPalindromicDensity.lean#L46), [`characteristic_palindromicDensity_exceptional_eq`](../Thesis/SturmianPalindromicDensity.lean#L53), [`characteristic_palindromicDensity_exceptional_measure_and_dimension`](../Thesis/SturmianPalindromicDensity.lean#L63), [`characteristic_palindromicDensity_spectrum`](../Thesis/SturmianPalindromicDensity.lean#L72), [`characteristic_palindromicDensity_constant_tail`](../Thesis/SturmianPalindromicDensity.lean#L84), [`density_ones_tail`](../Thesis/SturmianConstantTail.lean#L100), [`density_twos_tail`](../Thesis/SturmianConstantTail.lean#L116), [`constant_tail_values_tendsto_half`](../Thesis/SturmianConstantTail.lean#L144), [`constant_tail_values_strictAnti`](../Thesis/SturmianConstantTail.lean#L152), [`palindromicDensity_insert`](../Thesis/PalindromicDensityReal.lean#L130) |
| <a name="node-c12"></a> **C12** Классические факты | Частично | Проверены полный список палиндромных префиксов слова Фибоначчи и богатство его конечных факторов. Богатство всех штурмовых факторов в общем случае остаётся открытым для этой формализации. [`infiniteWord_palPrefix_iff`](../Thesis/FibonacciCompletePrefixes.lean#L101), [`rich_word`](../Thesis/FibonacciRichness.lean#L36), [`rich_factor`](../Thesis/FibonacciRichness.lean#L58) |

## 3.8  Скрученные повторы и динамика

| Узел | Статус Lean | Покрытие и ссылки |
|---|---|---|
| <a name="node-d0"></a> **D0** Предл. 3.8.1 / 3.8.4 | Доказано | Доказана формула цифр и соответствие конечных итераций подстановки префиксам неподвижного слова. [`iterate_cycleSubstitution`](../Thesis/ThueMorseCyclicAlphabet.lean#L87), [`cycleAlphabetEquiv_finiteWord`](../Thesis/ThueMorseCyclicAlphabet.lean#L173), [`wordOnCycle_unique_fixedPoint`](../Thesis/ThueMorseCyclicAlphabet.lean#L63) |
| <a name="node-d1"></a> **D1** Лемма 3.8.4 | Частично | Проверены переход к сравнению соседних блоков и используемая в классификации арифметика переносов. Все формулы узла с явной функцией показателя делимости не отмечены. [`strongBlockRepeat_iff_adjacent`](../Thesis/ThueMorseCyclicAlphabet.lean#L15), [`strongBlockRepeat_wordOnCycle_iff`](../Thesis/ThueMorseCyclicAlphabet.lean#L208), [`repeat_of_critical_bound`](../Thesis/ThueMorseClassification.lean#L143), [`critical_bound_of_repeat`](../Thesis/ThueMorseClassification.lean#L375) |
| <a name="node-d2"></a> **D2** Леммы 3.8.1–3.8.3 | Частично | Редукция окна и двоичное ограничение входят в доказательство необходимости. Весь пакет отдельных лемм 3.8.1–3.8.3 в исходных формулировках не отмечен. [`binary_twist_necessary`](../Thesis/ThueMorse.lean#L156) |
| <a name="node-d3"></a> **D3** Теорема 3.8.2 | Доказано | Бинарный критерий избегания доказан на исходном алфавите для любого целого показателя перестановки. [`wordOnCycle_binary_avoidance`](../Thesis/ThueMorseCyclicAlphabet.lean#L247) |
| <a name="node-e5"></a> **E5** Теорема 3.8.5 | С уточнением | Доказаны периодический и непериодический случаи с поправкой из исправленного TeX. При j' ≥ b частное в формуле не превосходит 2. [`wordOnCycle_periodic_case`](../Thesis/ThueMorseCyclicAlphabet.lean#L227), [`wordOnCycle_twisted_critical_exponent`](../Thesis/ThueMorseCyclicAlphabet.lean#L239) |
| <a name="node-d4"></a> **D4** Следствие 3.8.6 | Доказано | Проверены отсутствие финального периода и бинарные частные случаи через явный порог 2 или 4. [`not_eventually_periodic_word`](../Thesis/ThueMorseRecurrence.lean#L70), [`wordOnCycle_binary_threshold`](../Thesis/ThueMorseCyclicAlphabet.lean#L261) |
| <a name="node-d5"></a> **D5** Теорема 3.8.7 (1,2,4,5) | Доказано | Проверены пункты (1), (2), (4) и (5) для одностороннего замыкания орбиты. [`finiteWord_dynamics`](../Thesis/ThueMorseDynamics.lean#L11), [`iterate_cycleSubstitution_contains_letter`](../Thesis/ThueMorseCyclicAlphabet.lean#L181) |
| <a name="node-d6"></a> **D6** Теорема 3.8.7 (3) | Доказано | Проверены пункт (3), обе границы сложности при положительной длине и нулевая энтропия. [`finiteWord_dynamics`](../Thesis/ThueMorseDynamics.lean#L11) |
| <a name="node-d7"></a> **D7** Следствие 3.8.8 | Доказано | Запрет перенесён на всё замыкание орбиты по равенству языков факторов. [`orbitClosure_factorLanguage_eq`](../Thesis/ThueMorseSubshift.lean#L11), [`orbitClosure_no_long_twisted_repeat`](../Thesis/ThueMorseSubshift.lean#L54) |
| <a name="node-n1"></a> **N1** Наблюдение 3.8.3 | Без отметки | — |
| <a name="node-d8"></a> **D8** Внешние классические факты | Частично | Проверены используемый случай строгой эргодичности для примитивных подстановок постоянной длины и нижняя оценка Морса–Хедлунда. [`primitive_constantLength_unique_measure`](../Thesis/PrimitiveSubstitutionErgodicity.lean#L12), [`complexity_ge_of_not_eventually_periodic`](../Thesis/ThueMorseComplexity.lean#L76) |
| <a name="node-d9"></a> **D9** Tromp–Shallit, 1995 | Без отметки | — |

## 5.1  Деревья и индексы

| Узел | Статус Lean | Покрытие и ссылки |
|---|---|---|
| <a name="node-g0"></a> **G0** Штурмов язык | Доказано | Для характеристического слова проверены p(k)=k+1 и идентификация правого специального фактора с обращением префикса. Число специальных факторов следует из разности сложностей. [`characteristic_complexity`](../Thesis/SturmianFactorTree.lean#L12), [`characteristic_rightSpecial_eq_reversedPrefix`](../Thesis/SturmianMechanical.lean#L201), [`complexity_succ_eq_add_rightSpecials`](../Thesis/FactorTreeSpecial.lean#L43) |
| <a name="node-g1"></a> **G1** Предл. 5.1.1 | Без отметки | — |
| <a name="node-g2"></a> **G2** Предл. 5.1.2 | Без отметки | — |
| <a name="node-g3"></a> **G3** Теорема 5.1.3 | Доказано | Проверены число вершин и все четыре индекса для дерева в SimpleGraph. [`characteristic_factorGraph_indices`](../Thesis/FactorTreeGraphIndices.lean#L70) |
| <a name="node-n2"></a> **N2** Гипотеза 1 | Без отметки | — |
| <a name="node-g4"></a> **G4** Рассуждение рецензента | Без отметки | — |

## 3.7–3.8  Метрика

| Узел | Статус Lean | Покрытие и ссылки |
|---|---|---|
| <a name="node-n3"></a> **N3** Предл. 3.7.1 | Доказано | Для замкнутых подсдвигов доказаны метрические свойства, согласованность с топологией произведения, компактность, полнота и липшицева оценка для отображения. [`distance_nonneg`](../Thesis/SymbolicLatticeMetric.lean#L82), [`distance_comm`](../Thesis/SymbolicLatticeMetric.lean#L93), [`distance_triangle`](../Thesis/SymbolicLatticeMetric.lean#L98), [`eq_of_distance_eq_zero`](../Thesis/SymbolicLatticeMetric.lean#L108), [`isOpen_iff_distance`](../Thesis/SymbolicLatticeTopology.lean#L119), [`compact_and_complete_of_closed`](../Thesis/SymbolicLatticeTopology.lean#L158), [`embedding_lipschitz`](../Thesis/SymbolicLatticeTopology.lean#L176) |
| <a name="node-m1"></a> **M1** Предл. 3.8.9 | Доказано | Доказана липшицевость сдвига с константой 2. [`shift_lipschitz`](../Thesis/SymbolicLatticeTopology.lean#L167) |

## 4.2  Разрезание полимино

| Узел | Статус Lean | Покрытие и ссылки |
|---|---|---|
| <a name="node-q0"></a> **Q0** Модель разрезания | Определение | Задана геометрическая модель полного удаления линий из объединения квадратов. [`cellSquare`](../Thesis/PolyominoGeometry.lean#L13), [`remaining`](../Thesis/PolyominoGeometry.lean#L19), [`GeometricallySeparated`](../Thesis/PolyominoGeometry.lean#L23) |
| <a name="node-q1"></a> **Q1** Теорема 4.2.1 | С уточнением | Формула доказана для полимино, связного по общим сторонам, включая прямоугольник. Для касания только в вершине проверен контрпример. [`minimum_geometric_cuts`](../Thesis/PolyominoGeometry.lean#L268), [`rectangle_minimum_geometric_cuts`](../Thesis/PolyominoGeometry.lean#L274), [`corner_contact_counterexample`](../Thesis/PolyominoGeometry.lean#L285) |
