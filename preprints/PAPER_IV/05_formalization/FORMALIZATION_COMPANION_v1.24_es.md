# Complemento formal de Paper IV

**Juan Pablo Traverso Gianini**

**Preprint:** versión 1.24, 19 de octubre de 2026.

Este documento describe la formalización congelada que respalda *Particiones de cliques con defecto simplicial enraizado: estabilidad cuantitativa y cotas agudas para órdenes grandes*. Acompaña la revisión editorial del manuscrito; los enunciados matemáticos y el congelado Lean permanecen intactos. Los números de secciones, ecuaciones y teoremas se refieren al manuscrito principal, salvo indicación contraria. Las referencias [1–23] conservan su bibliografía.

## 1. Identidad de fuentes y alcance de la verificación

| Elemento | Valor congelado |
|:--|:--|
| Lean y Mathlib | v4.28.0 |
| Corte de fuentes | `piv-v12-fb459343d234` |
| Módulos de fuentes principales | 607 |
| Entradas de fuentes/configuración/documentación | 615 |
| Objetivos de auditoría seleccionados | 19 |
| Exportaciones literales mediante `import PaperIV` | 224 |
| Salidas de axiomas registradas | 461; no es una cuenta de teoremas distintos |

El SHA-256 del manifiesto de fuentes es `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5`. El SHA-256 del archivo de sólo fuentes es `cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6`. Identifican el paquete formal original, no los nuevos PDF editoriales.

El [paquete congelado](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/05_formalization) y la [evidencia de compilación registrada](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/03_reproducibility) están disponibles en el repositorio de la serie. El DOI de concepto de la serie es [10.5281/zenodo.21273143](https://doi.org/10.5281/zenodo.21273143). La edición anterior del manuscrito y su depósito siguen disponibles; el congelado de fuentes es el mismo.

El suplemento Lean identificado de esta versión usa Lean y Mathlib v4.28.0. Las declaraciones finales no reciben como argumentos el redondeo, la existencia del óptimo ni el constructor cercano: los invocan como teoremas demostrados en sus dependencias. Los axiomas fundacionales permitidos se distinguen de cualquier hipótesis matemática adicional.

La reconstrucción registrada cubre los 607 módulos: se verificaron y reutilizaron 421 objetos compilados en el primer segmento tras un reinicio, y el segmento reanudado compiló 186 módulos. Los 19 objetivos seleccionados se ejecutaron de nuevo con código de salida cero. Sus 461 salidas de axiomas usan sólo `propext`, `Classical.choice` y `Quot.sound`, o subconjuntos. Los registros distinguen identidad fuente, compilación, disponibilidad de exportaciones y comprobación transitiva de axiomas. Ninguna cuenta afirma que cada frase del manuscrito sea un teorema exportado por separado.

El informe externo consolidado de v1.22-r4 registra PASS para E0–E8 dentro de su alcance documentado. Ese informe y los registros de compilación siguen siendo evidencia del congelado identificado. No constituyen una revisión externa nueva de v1.24. La revisión editorial presente comprueba traslados, conservación de enunciados y renderizado documental; no se afirma una compilación Lean ni una verificación matemática nueva.

## 2. Enunciados matemáticos y declaraciones exportadas

Se omite el prefijo común `PaperIV` donde se indica. El mapa siguiente conserva las etiquetas originales de los teoremas; trasladarlo fuera del manuscrito principal no modifica la interfaz formal.

| Resultado | Declaración Lean |
|:--|:--|
| Teorema A, forma aditiva | `Erdos81AllOrders.erdos81_all_orders_additive` |
| Teorema B, cota superior | `Erdos81Unconditional.erdos81_cliquePartition` |
| Teorema B, máximo | `PaperTheorems.erdos81_max_eq` |
| Teorema 3.1 | `RC01Final.rc01_uniformRoundingTarget` |
| Corolario 3.5 | `FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs` |
| Dicotomía (1.5) | `HybridDichotomy.chordal_far_or_nearStructure` |
| Teorema 5.0, ventana reforzada | `NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp` |
| Teorema 5.0, interfaz anterior | `NearH1LocalConstructor.exists_near_partition_paid_by_root` |
| Corolario 5.4, tamaño y densidad | `NearCriticalDichotomy.chordal_far_or_criticalRoot`, `chordal_far_or_edge_density` |
| Coeficiente cuadrático óptimo | `SharpConstantOptimality.erdos81_quadratic_constant_optimal`, `erdos81_quadratic_constant_isLeast` |
| Teorema 6.1, forma reforzada | `IntegralStability.chordal_linear_stability_sixteen` |
| Teorema 6.1, interfaz anterior | `IntegralStability.chordal_linear_stability` |
| Corolario 6.1a, número de piezas | `RootPartitionStability.chordal_partition_stability` |
| Corolario 6.1a, cotas reales conjuntas de piezas y aristas | `SublinearResearch.chordal_joint_stability_real` en `PublicationStability` |
| Identidad (6.7b) | `RootPartitionStability.sum_rootPieceDefect_eq` |
| Corolario 6.2 | `ExtremalClassification.chordal_extremal_classification` |
| Proposición D.3 | `SplitMixedGap.mixed_gap_zero` junto con la construcción acotada de `SplitCompleteSharpValue` |

En la tabla de extensiones siguiente, el prefijo es `PaperIV.SublinearResearch`, salvo la entrada E32 indicada.

| Enunciado | Declaración |
|:--|:--|
| Cotas cordales reales con una misma raíz, incluida la masa de aristas | `chordal_joint_stability_real` |
| Teorema C′ y (6.12)–(6.13) | `fixed_defect_joint_stability_real` |
| Parámetros explícitos y clasificación | `FixedExplicit.fixed_defect_stability_explicit` |
| Cota de edición hacia tamaño óptimo (6.17) | `fixed_defect_exact_extremal_edit_real` |
| Clasificación irrestricta de la igualdad | `E32.cp_classification_of_theoremCPrimeC`, con la clasificación demostrada arriba y el ensamblaje histórico de remoción inducida [23] (véase §3 de este complemento) |
| Cota finita (6.22) | `certified_shifted_fractional_bound_all_orders` |
| Cota finita (6.23) | `certified_refined_fractional_bound_all_orders` |
| Versiones integrales uniformes | `uniform_shifted_partition_bound`; `uniform_refined_partition_bound` |
| Aproximación secuencial con órdenes arbitrarios | `sequence_arbitrary_orders_partition_bound` |
| Estabilidad secuencial con una raíz | `sequence_arbitrary_orders_stability` |

Las interfaces finitas con una misma raíz toman déficits reales. La interfaz secuencial registra parámetros racionales de error y exceso. Esta diferencia se conserva al comparar el manuscrito con los tipos elaborados.

**Definiciones literales.** Los fragmentos siguientes reproducen las definiciones y las cabeceras de los teoremas, omitiendo sus demostraciones, no sus hipótesis. En el primer fragmento el espacio es `SimpleGraph`; en los tres siguientes es `PaperIV.FarRounding`, con \(V\) finito, igualdad decidible y adyacencia decidible para \(G\). La última definición está en `PaperIV`. Las fuentes son `PaperIV/ChordalStructure.lean` (cordalidad), `PaperIV/FarRounding.lean` (pares y particiones) y `PaperIV/TargetEnvelope.lean` (tamaño objetivo), dentro del paquete congelado enlazado en §1 de este complemento.

```lean
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → 4 ≤ c.length →
    ∃ x y : V, x ∈ c.support ∧ y ∈ c.support ∧ G.Adj x y ∧ s(x, y) ∉ c.edges
```

```lean
def pairs (K : Finset V) : Finset (Sym2 V) := K.sym2.filter fun e => ¬ e.IsDiag

structure CliquePartition where
  pieces : Finset (Finset V)
  isClique : ∀ K ∈ pieces, ∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b
  two_le_card : ∀ K ∈ pieces, 2 ≤ K.card
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)
  covers : pieces.biUnion pairs = G.edgeFinset

def CliquePartition.size (Q : CliquePartition G) : ℕ := Q.pieces.card

def CliquePartition.OrderAtMost (Q : CliquePartition G) (r : ℕ) : Prop :=
  ∀ K ∈ Q.pieces, K.card ≤ r
```

```lean
def targetSize (n : ℕ) : ℕ := n * (n + 1) / 6
```

La división de naturales implementa el piso de \(M(n)\). El símbolo expositivo \(c_4\) designa el mínimo sobre esas particiones con `OrderAtMost 4`; el enunciado exportado no presupone una función mínimo, sino que entrega directamente una partición testigo. La cordalidad de `FarRounding` es un alias literal de la definición por ciclos anterior.

**Teoremas exportados.** En `PaperIV.Erdos81AllOrders` y `PaperIV.Erdos81Unconditional`, respectivamente, las cabeceras exactas son:

```lean
theorem erdos81_all_orders_additive :
    ∃ b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n + b
```

```lean
theorem erdos81_cliquePartition :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n
```

Estas cabeceras permiten comprobar el orden de cuantificadores y la cobertura exacta sin inferirlos del nombre del teorema. La auditoría adjunta no contiene `sorryAx` entre los axiomas de las declaraciones examinadas. El informe complementario distingue esa comprobación transitiva de la búsqueda textual de `native_decide` en las fuentes del proyecto y de una reconstrucción completa de las dependencias.

## 3. Dependencias, adaptadores y atribución

| Resultado en el texto | Módulo de referencia |
|:--|:--|
| **Entradas y construcción** | |
| Óptimo racional alcanzado | `PaperI.FiniteLPDuality`, `CertifiedOptimumExistence` |
| Redondeo mixto uniforme, Teorema 3.1 | `RC01Final`, `MixedRoundingAdapter`; infraestructura `Nibble.*` de Paper III |
| Corolario 3.5, régimen lejano para todos los grafos | `FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs`; versión explícita en `E17.ExplicitFarAssembly` |
| Limpieza mejorada completa y umbral explícito | `E17.Cleanup`, `E17.FarBudget`, `E17.ExplicitFarRounding`, `E17.ExplicitFarAssembly`; constantes de `E18` y `E19` |
| Selección fraccional por nibble, Paper III | `Nibble.FracNibbleLE`, `Nibble.FracNibbleRepaired`; adaptadores `PaperIIISlackNibbleAdapter`, `PaperIIINibbleAdapter` |
| Localización, raíz y ventana crítica | `NearH1Localization`, `NearRootWindow`, `RootRegularizationBridge` |
| Dicotomía e interfaz absorbible | `HybridDichotomy`, `SeparationAbsorptionRoute` |
| Contabilidad y partición cercana | `RD09PhysicalLedger`, `NearH1FinalAssembly`, `NearH1LocalConstructor` |
| **Conclusiones extremales** | |
| Cota aguda y máximo eventual | `Erdos81Unconditional`, `PaperTheorems` |
| Cotas para todos los órdenes | `Erdos81AllOrders`; cota explícita en `ExplicitThreshold` |
| Defecto enraizado fijo y máximo, Teorema C | `DefectExplicitPublication`; ensamblaje explícito `E34.L11Main`; testigo inferior `DefectSharpPublication` |
| Necesidad del orden cuatro, Proposición D.2 | `DefectSharpPublication.order_three_insufficient`, `E11K10` |
| Presupuesto general y paso a \(\operatorname{cp}\) | `LossBudget`, `SplitMixedGap` |
| Estabilidad del grafo, estabilidad de particiones y clasificación extremal | `IntegralStability`, `RootPartitionStability`, `ExtremalClassification` |
| Valor completo-split y núcleos | `SplitCompleteSharpValue`, `SplitCompleteRigidity` |
| Defecto de partición y coeficientes óptimos | `SplitCompleteDefect`, `LinearCoefficient`, `SharpConstantOptimality` |
| Densidad de aristas en la rama crítica | `NearEdgeDensity`, `NearCriticalDichotomy` |
| Igualdad de óptimos mixtos, Apéndice D.2 | `SplitMixedGap`, `SplitCompleteSharpValue` |
| **Herramientas complementarias** | |
| Absorción compatible con presupuesto | `SpreadAbsorptionCompatibility` |
| Reserva equilibrada, Apéndice B.2 | `BalancedReserve`, `Nibble.BeckFiala` de Paper III |
| Completación con cuatro anfitriones, Apéndice B.3 | `FourHostClosure`; Vizing y `MultiHostTriangleLift` |
| Reserva exacta y sensibilidad del umbral | `ReserveIdentity`, `NearThresholdSensitivity` |
| Estructura cordal reutilizable | `CliqueTree` |

**Mapa de módulos.** Los prefijos `PaperI`, `Nibble` y `MixedRounding` señalan, respectivamente, el desarrollo racional vinculado a Paper I, la infraestructura de nibble de Paper III y la biblioteca neutral del modelo mixto. Los prefijos `E17`, `E18`, `E19` y `A4S1` identifican los módulos de los incrementos integrados en el proyecto; los demás nombres sin prefijo pertenecen a `PaperIV`; `MixedRoundingAdapter` es un adaptador de ese espacio hacia la biblioteca `MixedRounding`. RC01 incorpora y adapta herramientas de Paper III, pero su ensamblaje mixto de dos cuotas es el de la Sección 3 de esta investigación. La tabla relaciona resultados y fuentes; el suplemento conserva la lista exacta de dependencias.

La estructura cordal y Dirac proceden de la contribución de Paper II, portada en `ChordalStructure`. El lema de regularidad de Szemerédi se reutiliza de Mathlib; la construcción y los adaptadores de perfiles limpios y de selección mixta pertenecen a Paper IV. Esta procedencia se distingue de la ubicación actual de un archivo bajo `PaperIV`.

La configuración declara Mathlib como paquete de terceros y una selección de módulos `Nibble` de Paper III como dependencia local de la serie. `ConeAudit` recorre los tipos y términos de prueba de las declaraciones seleccionadas y comprueba que sus dependencias transitivas no contengan nombres bajo la raíz `Erdos81`, utilizada por [5]. Nuestros módulos `PaperIV.Erdos81Unconditional` y `PaperIV.Erdos81AllOrders` tienen raíz de espacio de nombres `PaperIV`; no son la raíz excluida Erdos81 que usa [5]. La ausencia de estos nombres es un resultado de auditoría reproducible, no una inferencia de la lista de importaciones. Su alcance es preciso: certifica esa exclusión en el corte examinado; por sí sola no detectaría código trasladado y renombrado ni determinaría la procedencia histórica de cada argumento. La atribución de fuentes se documenta por separado. El mismo control de espacios de nombres no permite emitir un veredicto sobre [15]. La extensión utiliza el método de estrella con signos de [15, Lema 3.1] y el método de remoción de [22]; demostrar sus implementaciones en este suplemento no convierte esos métodos en nuevos.

La interfaz pública del Teorema C en esta revisión es `DefectExplicitPublication`: utiliza `E34.theoremC_fully_explicit_final` y el testigo inferior irrestricto ya demostrado en `DefectSharpPublication`. El ensamblaje existencial anterior no es la prueba seleccionada para el Teorema C. Su localización utiliza remoción inducida de Alon–Shapira [23]; el ensamblaje explícito seleccionado utiliza, en cambio, el desarrollo de remoción cordal polinómica de [22]. El control adicional `FDCheck.ASCheck` recorre términos de prueba y tipos para comprobar la exclusión de los resultados de remoción identificados en estas declaraciones seleccionadas. Esto no excluye el espacio de nombres `AlonShapira`: se siguen usando definiciones compartidas de cordalidad, distancia de edición y copias inducidas.

Hay una excepción concreta a esta comparación de dependencias. La clasificación irrestricta de la igualdad del Corolario 6.3, (6.18), se exporta mediante `E32.cp_classification_of_theoremCPrimeC`; esa declaración y `E32.ref15Theorem11_of_theoremCPrimeC` todavía utilizan el ensamblaje histórico a través de `E32.theoremC_at`. Sus pruebas incluyen, por tanto, la cadena de remoción inducida de [23]. Todos esos lemas están demostrados en las fuentes congeladas con axiomas estándar. El control de exclusión para el Teorema C explícito y las declaraciones de estabilidad seleccionadas no debe extenderse a estas interfaces de clasificación.

### 3.1. Recursos y las dos convenciones de ganancia

El refinamiento de representación del mapa original de prueba se verifica en `MixedRoundingAdapter`. El adaptador identifica las aristas de una pieza y el predicado de copia admisible, transporta las capacidades de un empaquetamiento fraccional y prueba la igualdad de valores mediante `value_toFarFrac`. Para un empaquetamiento entero, `gain_toFarPacking` conserva la ganancia. Por tanto, el Teorema 3.1 puede utilizarse a través de esta presentación neutral sin cambiar el presupuesto (1.3). Esto no constituye una nueva demostración del redondeo.

Hay dos funciones llamadas `gainOf` cuyo dominio de uso debe distinguirse. `Model.gainOf` vale dos en cardinal tres, cinco en cardinal cuatro y cero en los demás cardinales. `FarRounding.gainOf` vale \(\binom{|K|}{2}\mathbin{\dot-}1\), donde \(\dot-\) es la resta truncada en los naturales. Coinciden en cardinales de cero a cuatro, pero desde cinco dejan de coincidir. En los ítems mixtos, que tienen cardinal tres o cuatro, el transporte es legítimo. Para particiones irrestrictas, como las de la Sección 6.4, se usa la cuenta de aristas o `FarRounding.gainOf`; nunca se sustituye por la función de ganancia acotada de `Model`. Puesto que las piezas de una partición tienen al menos dos vértices, allí la resta truncada coincide con la resta ordinaria.

### 3.2. Construcción y cuentas conservadas

El nibble de rango acotado se reutiliza mediante `PaperIIISlackNibbleAdapter.boundedRankNibbleAt`. La construcción de las dos cuotas está en `MarkedQuotaSlackGate.slackMarkedQuotaNibbleAt_proved`; el emparejamiento de soportes triangulares y su realización física están en `MarkedQuotaPairing` y `JointTwoQuotaPhysical`. La escala conjunta de codegrado corresponde a `RC01CleanedGate.cleanedPacking_joint_codegree_le_of_served_patterns`. Los perfiles tienen masa a lo sumo \(t^2\), no uno: es la normalización física de `RC01PatternMassScale`.

Para el camino mixto, `VertexCopyMonotone.two_mul_F4_le_add` prueba la desigualdad de las dos direcciones. `VertexCopyGate` selecciona el paso y su potencial finito; `GatedTerminalSplit.exists_split_terminal_symmetrizationPath` entrega la sucesión completa. La cuenta local se construye en `NearH1WindowAccounts`, antes de importarla en `NearH1Localization`. Esta dirección de dependencias corresponde al orden lógico explicado en el Lema 4.2.

La extracción de la clique y la calibración están en `ChordalCoreMissing` y `NearH1CalibratedRoot`. `Regularization`, `RegularizationBounds` y `RegularizedRootGoal` prueban las propiedades de la raíz que utiliza `RootRegularizationBridge`. Finalmente, `NearH1PhaseI`, `RD09FactorCandidateMoments` y `RD09FactorCandidateAverage` producen las dos cuentas; `NearH1FinalAssembly` las une usando la misma primera asignación y sus enlaces ocupados. No se aplica la segunda fase a una copia independiente de los recursos.

El Teorema 5.0 tiene una forma reforzada, `NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp`, que añade \(|3|R|-n|\le n/50\) al constructor físico; la interfaz anterior `exists_near_partition_paid_by_root` se conserva como corolario. La reserva reforzada de (5.15a) se conserva para ese mismo testigo en `NearStructureWitness.accounts_count_le_improved`; `IntegralStability.chordal_linear_stability_sixteen` y `RootPartitionStability.chordal_partition_stability` la utilizan sin recombinar raíces ni empaquetamientos. La selección cíclica de la fase I está en `RD09PaddedL1Mass`; la última evaluación de la fase II, en `H1ImprovedConstants.l10_of_raw_rd09L2`. Los regímenes del comparador de (5.1a) se comprueban en `SplitComparatorResidual.residual_sq_le_of_near_split_universal`. La reserva (D.8) es `ReserveIdentity.targetSize_eq_baseline_add_reserve`; la contracción mejorada corresponde a `NearThresholdSensitivity.descent_threshold_maximal_barrier` y `near_threshold_binding`. Los resultados de geometría crítica están en `NearRootWindow`, `NearEdgeDensity` y `NearCriticalDichotomy`.

Los resultados de extensión tienen puntos de entrada públicos separados. El Teorema C y su máximo son `PaperIV.DefectExplicitPublication.rooted_defect_eventual` y `rooted_defect_maximum`; el espacio de nombres histórico `DefectSharpPublication` conserva el testigo inferior y `order_three_insufficient` para la Proposición D.2. `E35.theoremC_tower` y sus variantes uniformes dan el Corolario 6.6. La cuenta completa (3.11) es `E17Bridge.improved_far_loss_explicit`. El Corolario 3.5 con umbral explícito es `E17Bridge.ExplicitAssembly.farRegime_allGraphs_explicit`. Finalmente, `PaperIV.ExplicitThreshold.erdos81_sharp_explicit` y `erdos81_all_orders_bounded_additive` dan el resultado global con la torre de §6.3. Estos nombres identifican declaraciones, no nuevas hipótesis.

### 3.3. Alcance respecto de otros desarrollos formales

El alcance formal difiere del documentado por [5] en el commit citado. Su archivo `lean/FORMALIZATION_STATUS.md` declara una verificación condicionada a `ExternalInputs.Inputs`: Vizing, Häggkvist–Janssen y una transferencia de empaquetamiento que incluye certificados de optimalidad racional. Esas entradas son parámetros explícitos, no axiomas ocultos. Aquí se descargan las entradas empleadas por nuestra cadena, incluido Vizing; no se utiliza Häggkvist–Janssen. La comparación concierne a lo comprobado por cada desarrollo Lean: no afirma que la demostración matemática de [5] quede condicionada a conjeturas.

Las contribuciones reutilizables tienen referencias propias. El empaquetamiento de triángulos suma-cero corresponde al PR #348 de Lean Pool [12], <https://github.com/Vilin97/lean-pool/pull/348>, fusionado en el commit `540d8e3`. Los emparejamientos por grado mínimo y su selección ponderada corresponden al PR #420 [9], <https://github.com/Vilin97/lean-pool/pull/420>, fusionado en `d1de6d2`. Las fuentes de la serie conservan los antecedentes y adaptaciones de Vizing y Beck–Fiala. La atribución de las formalizaciones se distingue de la autoría de los teoremas clásicos.

Lean [10] y Mathlib [11] proporcionan el entorno de comprobación. La auditoría del código no reemplaza la revisión humana de las definiciones ni la correspondencia entre un enunciado formal y su expresión en el manuscrito. Los experimentos orientaron la búsqueda y detectaron afirmaciones falsas; no se usan como premisas de universalidad.

El constructor formal utilizado no invoca los resultados de [15] ni los módulos históricos de la construcción sustituida. La cota de listas y la ventana de capacidad de la primera fase coinciden en forma con condiciones de [15, Lema 4.1 y (4.4)]. Aquí se justifican mediante hospedaje diádico, promedio de desplazamientos cíclicos y absorción equilibrada. Esta comparación identifica los mecanismos y sus coincidencias; no reclama prioridad para esas condiciones ni deduce independencia histórica del control de dependencias de §3 de este complemento.

## 4. Precisiones para la correspondencia con el manuscrito

Las distinciones siguientes se conservan al retirar los nombres de implementación de la exposición. Evitan identificar un enunciado matemático con un tipo Lean más fuerte o con otros cuantificadores.

- La construcción de §6.1 usa triángulos y aristas; la interfaz pública auditada proporciona una partición de orden a lo sumo cuatro y una cota inferior irrestricta.
- Las declaraciones de optimalidad cuadrática y lineal usan coeficientes racionales. El manuscrito explica el paso a coeficientes reales por aproximación racional.
- `recover_clique_from_edit` toma \(u\ge0\) racional; la prueba escrita también vale para \(u\ge0\) real.
- La Proposición G.1 usa precisión racional en la declaración Lean y comparaciones exponenciales reales.
- La formulación de anchura del Apéndice G.1 usa árboles de cliques con cardinalidad acotada de las bolsas; no se apoya en una definición general de treewidth de Mathlib.
- El Apéndice G.2 no formaliza una restricción cordal de la implicación limpieza–redondeo. La obstrucción universal no es una cota inferior para todo método de redondeo cordal.

### 4.1. Una premisa numérica existente escrita explícitamente

La prosa anterior de F.5 remitía a `thm2_ineq` por nombre. La nueva prosa imprime su conclusión existente, con \(m=m_{11}(\varepsilon,K)\), \(B=B_{11}(\varepsilon,K)\) y \(\delta_{11}\) como en (F.11). La fuente es `E34/L11Params.lean`, líneas 289–292. Sus hipótesis son \(0<\varepsilon<1\) y \(1\le K\); el párrafo anterior de F.5 proporciona las más fuertes \(\varepsilon<1/2\) y \(K\ge1\). Se desarrolla una premisa citada, no una estimación ni prueba nueva.

### 4.2. Mapa de referencias a código trasladadas

| Lugar del manuscrito | Declaraciones o módulos formales |
|:--|:--|
| 1.1. La condición común: presupuesto de pérdida | `LossBudget.budget_iff` |
| 1.2. Dicotomía estructural y mecanismos de resolución | `NearStructureWitness` |
| 5.3. Las tres cuentas que pagan la construcción | `isSpokeCompatible_surviving_canonicalBad`, `RD09SpokeCompatibility.card_union_phases` |
| 6.2. El máximo eventual | `SplitCompleteRigidity.optimal_cores` |
| 6.2. El máximo eventual | `PaperTheorems.splitGraph_isChordal` |
| 6.3. Todos los órdenes y optimalidad del término lineal | `SharpConstantOptimality.erdos81_quadratic_constant_optimal`, `erdos81_quadratic_constant_isLeast` |
| 6.3. Todos los órdenes y optimalidad del término lineal | `LinearCoefficient.linear_coefficient_optimal` |
| 6.3. Todos los órdenes y optimalidad del término lineal | `LossBudget.erdos81_cp_form_all_orders`, `erdos81_cp_form` |
| 6.6. Estabilidad para defecto fijo sobre una misma raíz | `NormalizedDeficit`, `ResidualExcess`, `NormalizedCliqueCore`, `RootPartition`, `NormalizedStability` |
| 6.7. Cotas uniformes y defecto sublineal | `E35.Fexp_le_tower` |
| B.1. Absorción compatible con presupuesto | `SpreadAbsorptionCompatibility.exists_budgeted_compatible_spread_absorber` |
| B.2. Reservas equilibradas | `BalancedReserve.exists_balanced_reserve` |
| B.3. Remate con cuatro anfitriones | `FourHostClosure.exists_fourHost_packing` |
| C.2. Qué se descarta y por qué el umbral es uniforme | `RC01CleanFiber`, `RC01DeviationCleanup` |
| C.3. Un calendario explícito y su propagación | `SzemerediRegularity.initialBound` |
| C.3. Un calendario explícito y su propagación | `E18.NibbleSchedule`, `NibbleOracle`, `NibbleChain` |
| C.3. Un calendario explícito y su propagación | `E19.ScheduleBounds`, `E19.ChainBounds`, `E19.GateBounds` |
| C.3. Un calendario explícito y su propagación | `E18.Numeric`, `E19.Main` |
| C.3. Un calendario explícito y su propagación | `E35.NfarE_le_tower_poly` |
| D.1. El grafo completo a todo orden | `ThreeRegime.CompleteStateAllOrders` |
| D.1. El grafo completo a todo orden | `HalvingFrames` |
| D.1. El grafo completo a todo orden | `exists_packing`, `complete_state_closes` |
| D.2. Igualdad de óptimos mixtos en grafos completo-split | `SplitMixedGap.mixed_gap_zero`, `SplitCompleteSharpValue` |
| E.1. Constructor y cuentas | `IndepAllBounds`, `IndepAllParams` |
| E.1. Constructor y cuentas | `IndepAllPeel`, `IndepAllObstr` |
| E.1. Constructor y cuentas | `IndepAllBudget` |
| E.1. Constructor y cuentas | `IndepAllMain`, `ConstructorBudget` |
| E.2. Del terminal al teorema eventual | `E34.theoremC_fully_explicit_final` |
| E.4. Cuentas conservadas para la estabilidad con una misma raíz | `StrictParams` |
| E.4. Cuentas conservadas para la estabilidad con una misma raíz | `StrictBudget` |
| E.4. Cuentas conservadas para la estabilidad con una misma raíz | `ResidualExcess` |
| E.4. Cuentas conservadas para la estabilidad con una misma raíz | `AllInput.no_core_pairs` |
| E.4. Cuentas conservadas para la estabilidad con una misma raíz | `CoreCliqueAlternative` |
| E.4. Cuentas conservadas para la estabilidad con una misma raíz | `TemplateDistance`, `RootPartition`, `CliqueShiftArithmetic` |
| F.1. Parámetros explícitos para defecto fijo | `ExplicitFixedStability`, `E33.Assembly`, `E33.LocExplicit`, `E34.L11Main` |
| F.1. Parámetros explícitos para defecto fijo | `fixed_defect_stability_explicit` |
| F.2. Contabilidad fraccional por estrellas y órdenes pequeños | `RefinedFractionalBound`, `UniformFractionalBound`, `SmallOrderFractional` |
| F.3. Localización uniforme mediante edición hacia un cordal | `SublinearEdit` |
| F.3. Localización uniforme mediante edición hacia un cordal | `exists_clique_additive_defect`, `recover_clique_from_edit` |
| F.3. Localización uniforme mediante edición hacia un cordal | `SublinearStabilityTransfer` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `E34.indCopies_cycle_le` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `E34.coBipartite_edit_le` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `E34.exists_large_clique` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `E34.lemma3` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `E34.transfer` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `E34.lemma11_V` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `properOn_of_pinned` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `thm2_ineq` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `claim5_count`, `block_ineq` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `l11_caseA`, `l11_caseB1`, `l11_caseB2`, `E34.L11Main` |
| F.5. Lemas auxiliares y adaptaciones de remoción cordal | `E35.theoremC_tower`, `theoremC_tower_uniform`, `theoremC_tower_uniform_sMax`, `NfarE_le_tower_poly`, `PaperIV.DefectExplicitPublication`, `FDCheck.ASCheck`, `PaperIV.OptimalTemplateObstruction.shifted_template_witness`, `shifted_template_sqrt_witness`, `no_linear_optimal_template_bound`, `optimal_family_nonempty` |
| G.1. La cota para todos los órdenes y las brechas de empaquetamiento | `BoundedCliqueGap` |
| G.1. La cota para todos los órdenes y las brechas de empaquetamiento | `BoundedCliqueGap.chordal_gap_linear_cliqueFree` |
| G.1. La cota para todos los órdenes y las brechas de empaquetamiento | `exists_cliqueTree_width_le_iff_cliqueFree` |
| G.2. Una obstrucción cuantitativa a la limpieza de codegrado | `CleanupAtWith` |
| G.2. Una obstrucción cuantitativa a la limpieza de codegrado | `threshold_gt_exp`, `threshold_gt_exp_seventy_two`, `FarExploration.CleanupRigidVerdict` |
| G.2. Una obstrucción cuantitativa a la limpieza de codegrado | `threshold_superpolynomial` |
| G.2. Una obstrucción cuantitativa a la limpieza de codegrado | `CodegreeCleanupAt`, `UniformRoundingTarget` |

## 5. Reproducción y anexo separado

Ejecute lo siguiente desde el archivo de fuentes extraído, sin modificar, con la versión fijada en `lean-toolchain` y las dependencias fijadas en `lake-manifest.json`. El comando se documenta para reproducibilidad; no se ejecutó para esta revisión editorial.

```text
python tools/audit_publication.py
```

Lee los 19 objetivos de `FREEZE_SCOPE.json`, los ejecuta en serie y conserva registros individuales. Reimportar un módulo de auditoría compilado no equivale a ejecutar de nuevo sus comandos. La ejecución registrada está en `03_reproducibility/full_rebuild_v12_20260929_resume/`, con enlaces de procedencia al primer segmento. `ReleaseExportCheck` usa sólo `import PaperIV`; las auditorías nombradas inspeccionan sus propias listas de tipos y términos de prueba.

| Objetivo |
|:--|
| `PaperIV` |
| `PaperIV.Audit` |
| `PaperIV.ConeAudit` |
| `PaperIV.PublicationIncrementAudit` |
| `A4S1.IndepAllAudit` |
| `ThreeRegime.AxiomCheck` |
| `FarExploration.AxiomCheck` |
| `PaperIV.CliqueTreeAudit` |
| `E17.ImprovedFarRoundingAudit` |
| `E17.ExplicitFarAudit` |
| `PaperIV.ExplicitThresholdAudit` |
| `ReleaseExportCheck` |
| `PaperIVEditorial.ConstructorBudgetAudit` |
| `ResearchAudit` |
| `FDCheck.FinalAudit` |
| `E35.Audit` |
| `FDCheck.ASCheck` |
| `E34.Audit` |
| `PaperIV.OptimalTemplateObstructionAudit` |

El manifiesto literal de fuentes es `03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json`. El registro de exportación contiene 224 comandos `#check` literales. La auditoría del constructor cubre `PaperIV.Editorial.ConstructorBudget`, que conserva ambas conclusiones para una misma partición. Los espacios de extracción antiguos y los cortes de fuentes reemplazados permanecen como registros históricos en el repositorio de la serie; no son módulos adicionales del congelado descrito aquí.

`BoundedCliqueGap` es un anexo de fuentes separado que respalda el Apéndice G.1; no es una entrada de la prueba extremal principal. El SHA-256 de su archivo de fuentes es `2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d`. Sus 38 módulos fuente y su clausura de compilación de 50 módulos pertenecen a su compilación registrada distinta, no a la cuenta de 607 anterior.

## 6. Revisión de la prueba escrita y límites

**Alcance de la prueba escrita.** La tabla siguiente registra siete derivaciones examinadas en la revisión externa consolidada. Su evaluación, ACCEPTABLE_SUMMARY para cada fila, conserva el límite expositivo declarado sobre las estimaciones de segundo momento citadas en C.2. Un build satisfactorio verifica derivaciones formales, no la integridad de su exposición; la evaluación de la prueba escrita sigue siendo distinta de la compilación y de la revisión humana por pares. El historial de auditoría y las evaluaciones detalladas se conservan con la evidencia complementaria.

| Ubicación | Derivación por revisar, incluidas las cuentas desarrolladas |
|:--|:--|
| §5.1, (5.4) y (5.7) | Estimaciones de masa, grado, paleta y anchura tras regularizar |
| C.2, (3.8) y (3.10) | Conteos de descarte y retención con las convenciones de partición |
| Lema 3.2 y C.1–C.2 | Cotas inferiores de fibras desde pares regulares y su normalización |
| C.3, Tabla C.1 | Dominación numérica de las constantes del nibble e iteraciones de la torre |
| E.1 | Cotas de normalización previas al constructor terminal |
| E.1, (E.2b) y (E.2d) | Estimaciones terminales y presupuesto de tres casos |
| D.1 | Construcciones de marcos Bose/Skolem que sustentan la tabla de residuos |

Las comprobaciones experimentales de órdenes pequeños no se usan como premisas. Su documentación, incluidos los requisitos de completitud y certificación, pertenece al registro de investigación separado.

La biblioteca de árboles de cliques conserva contraejemplos a formulaciones sin las hipótesis adecuadas: una hoja no equivale por sí sola a un único vértice simplicial, y las afirmaciones sobre separadores deben tratar las bolsas repetidas y los casos degenerados. Estos resultados delimitan el uso de esa biblioteca; no añaden supuestos al teorema principal.

El registro editorial conserva los párrafos fuente exactos y cada sustitución. Las comprobaciones automáticas comparan ecuaciones mostradas, etiquetas y encabezados de resultados; las hipótesis y dependencias de prueba se revisan además en el cotejo entre fuente y manuscrito. Esas comprobaciones no certifican automáticamente la equivalencia semántica de toda la prosa. La declaración de IA y herramientas conserva sus atribuciones y responsabilidades; se ha retirado la frase de estado del borrador anterior.

## Uso de inteligencia artificial y herramientas computacionales

Se utilizaron Claude, de Anthropic, y ChatGPT/Codex, de OpenAI, para explorar argumentos, comprobarlos y preparar el manuscrito. Aristotle, de Harmonic, participó en la exploración de caminos, la búsqueda de contraejemplos, la elaboración de pruebas y su formalización y revisión en Lean; no sólo tradujo pruebas terminadas.

Certo [13], <https://github.com/jtraverso/certo-math>, y Jacobian [14], <https://github.com/morluto/jacobian>, son las herramientas computacionales usadas para explorar instancias, comprobar identidades y evaluar candidatos. El proyecto de [5] también acredita a Jacobian; su uso aquí se declara por separado de las dependencias lógicas de nuestra prueba formal. Los cálculos se revisaron según su alcance; una búsqueda finita no reemplaza una prueba universal.

El autor conserva la responsabilidad por los argumentos, las citas, el código y la presentación. Ningún sistema de IA figura como autor.

## Referencias

[1] P. Erdős, E. T. Ordman y Y. Zalcstein, «Clique partitions of chordal graphs», *Combinatorics, Probability and Computing* **2** (1993), 409–415.

[2] J. P. Traverso Gianini, *Reducción afín de perfiles para empaquetamientos fraccionales de triángulos en grafos split*, Paper I, preprint v1.3, 22 de agosto de 2026. Ediciones española e inglesa en el depósito conjunto v3, 23 de agosto de 2026. DOI de la versión consultada: <https://doi.org/10.5281/zenodo.22064657>; DOI de concepto: <https://doi.org/10.5281/zenodo.21273143>. Material complementario: <https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_I>.

[3] J. P. Traverso Gianini, *Extremizadores complete-split para un funcional fraccional de cobertura de triángulos en grafos cordales*, Paper II, preprint v1.2, 22 de agosto de 2026. Ediciones española e inglesa en el depósito conjunto v3, 23 de agosto de 2026. DOI de la versión consultada: <https://doi.org/10.5281/zenodo.22064657>; DOI de concepto: <https://doi.org/10.5281/zenodo.21273143>. Material complementario: <https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_II>.

[4] J. P. Traverso Gianini, *Particiones de cliques con error lineal en grafos split mediante empaquetamiento estructurado de triángulos*, Paper III, preprint v1.5, 23 de agosto de 2026. Ediciones española e inglesa en el depósito conjunto v3 de esa fecha. DOI de la versión consultada: <https://doi.org/10.5281/zenodo.22064657>; DOI de concepto: <https://doi.org/10.5281/zenodo.21273143>. Material complementario: <https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_III>.

[5] Anonymous, *Clique partitions of chordal graphs with linear error*, preprint, 8 de septiembre de 2026. Versión consultada el 20 de septiembre de 2026, commit `cbde8a0a0563372b23b1b39a44180d2c0fb02f44`. Manuscrito: <https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/manuscript/main.pdf>. Se conserva la firma que figura en el documento. El README de ese mismo commit acredita a Morluto por la prueba matemática, a N0zoM1z0 por el manuscrito y la implementación Lean, y a Jacobian de Preference Labs como parte del proyecto: <https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/README.md>. Estos créditos del repositorio se distinguen de la firma impresa en el manuscrito.

[6] P. E. Haxell y V. Rödl, «Integer and fractional packings in dense graphs», *Combinatorica* **21** (2001), 13–38.

[7] R. Yuster, «Integer and fractional packing of families of graphs», *Random Structures & Algorithms* **26** (2005), 110–118.

[8] T. F. Bloom, «Erdős Problem #81», *Erdős Problems*. Disponible en <https://www.erdosproblems.com/81>. Referencia de identificación del problema; este artículo no certifica el estado actual de revisión de las propuestas publicadas.

[9] J. P. Traverso Gianini y colaboradores de la formalización asistida, «Minimum-degree and spread matching theorems», contribución a *lean-pool*, PR #420, 2026. Disponible en <https://github.com/Vilin97/lean-pool/pull/420>; commit de fusión `d1de6d2`, 13 de septiembre de 2026. El historial y los encabezados conservan la atribución de la contribución asistida por Aristotle.

[10] L. de Moura y S. Ullrich, «The Lean 4 Theorem Prover and Programming Language», en *Automated Deduction – CADE 28*, LNCS **12699**, Springer, 2021, 625–635.

[11] The mathlib Community, «The Lean Mathematical Library», en *CPP 2020*, ACM, 2020, 367–381.

[12] J. P. Traverso Gianini, «Sum-zero triangle packing formalization», contribución de Paper III a *lean-pool*, PR #348, 2026. Disponible en <https://github.com/Vilin97/lean-pool/pull/348>; commit de fusión `540d8e3`, 25 de agosto de 2026. Véanse los créditos de formalización y de asistencia en las fuentes.

[13] J. P. Traverso Gianini, *Certo: herramientas computacionales con certificados verificables*. Disponible en <https://github.com/jtraverso/certo-math>. La versión utilizada en los experimentos debe fijarse junto con sus certificados en el suplemento.

[14] Morluto y colaboradores, *Jacobian: herramientas matemáticas componibles*. Disponible en <https://github.com/morluto/jacobian>. La atribución y las versiones de los componentes se conservan en el repositorio.

[15] O. Okechukwu, *Clique partitions and bounded simplicial defect*, arXiv:2609.20871v1, 15 de septiembre de 2026. Disponible en <https://arxiv.org/abs/2609.20871v1>. Consulta del 27 de septiembre de 2026.

[16] C. Henderson, H. Koerts, E. Roberge, S. Spirkl y R. Whitman, *Clique Partitions of Split Graphs*, proyecto anunciado en preparación en la página de investigación de R. Whitman: <https://sites.google.com/view/rebeccawhitman/research>. Consulta del 27 de septiembre de 2026; la página consultada no enlaza un manuscrito que permita comparar sus resultados.

[17] F. A. Behrend, «On Sets of Integers Which Contain No Three Terms in Arithmetical Progression», *Proceedings of the National Academy of Sciences* **32** (1946), 331–332. <https://doi.org/10.1073/pnas.32.12.331>. La constante usada en Apéndice G.2 corresponde a `Behrend.roth_lower_bound` de Mathlib v4.28.0.

[18] I. Z. Ruzsa y E. Szemerédi, «Triple systems with no six points carrying three triangles», *Combinatorics*, vol. II, Colloquia Mathematica Societatis János Bolyai **18**, North-Holland, 1978, 939–945. Registro bibliográfico del autor: <https://www.renyi.hu/~szemered/pub.html>.

[19] R. C. Bose, «On the construction of balanced incomplete block designs», *Annals of Eugenics* **9** (1939), 353–399. <https://doi.org/10.1111/j.1469-1809.1939.tb02219.x>.

[20] T. Skolem, «Some Remarks on the Triple Systems of Steiner», *Mathematica Scandinavica* **6** (1958), 273–280. <https://tidsskrift.dk/math/article/view/10551>.

[21] R. Cipollini, anuncio de prueba parcial para el problema 81 de Erdős, 10 de agosto de 2026. Resumen del autor: <https://www.erdosproblems.com/forum/thread/81/proof-claims#proof-claim-201>; manuscrito enlazado: <https://www.overleaf.com/read/thjptfhgnmxc>. Se cita por la cota anunciada con error subcuadrático, no como una entrada auditada independientemente.

[22] R. de Joannis de Verclos, *Chordal graphs are easily testable*, arXiv:1902.06135v1, 16 de febrero de 2019. Disponible en <https://arxiv.org/abs/1902.06135v1>. El argumento de remoción que sostiene el Apéndice F.3 se atribuye a este trabajo; su implementación y adaptaciones se documentan en el Apéndice F.5.

[23] N. Alon y A. Shapira, *A characterization of the (natural) graph properties testable with one-sided error*, SIAM Journal on Computing **37** (2008), 1703–1727. DOI: <https://doi.org/10.1137/06064888X>. Utilizado por el ensamblaje existencial histórico y por las interfaces de clasificación irrestricta identificadas en §3 de este complemento, no como el teorema de remoción seleccionado para el Teorema C público explícito.

