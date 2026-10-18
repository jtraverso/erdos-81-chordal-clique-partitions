# Artículo VI — Complemento de formalización y reproducibilidad

**Juan Pablo Traverso Gianini**  
**Preprint 1.0**  
**Fecha:** 18 de octubre de 2026  
**Derechos de autor:** © 2026 Juan Pablo Traverso Gianini. Este documento se distribuye bajo CC BY-NC 4.0.

## 1. Fuentes y punto de entrada

El [paquete público de fuentes](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_VI/05_formalization) contiene los enunciados y las demostraciones formales de Paper VI. Su objetivo predeterminado, `PaperVIRelease`, importa públicamente `PaperVI`, el alias de compatibilidad `PaperVIExtended` y `PaperVIRecourse`. La clausura completa de imports locales contiene 79 módulos. Incluye los Teoremas A–E, el intervalo de tamaños generales, los resultados intrínsecos y excepcionales, los apéndices y los resultados de prefijos, recourse y conectividad restringida all-K5 para joins completos de la Sección 10.

El toolchain es `leanprover/lean4:v4.35.0`; Mathlib está fijada en `56a005855ea17e0b0958f73ec801ae140b0a1679`. Las fuentes Lean del autor se distribuyen bajo Apache-2.0. Las cabeceras de copyright y SPDX conservan los créditos de autor y los avisos de terceros existentes. Estas cabeceras de licencia no cambian los tipos de los teoremas ni los cuerpos de sus demostraciones.

`PaperVIRelease.lean` SHA256: `05de8cc26e4077d04e74d9a15c1373e40f8c66ed32590df90c617509bf44acee`.

`SOURCE_CLOSURE.json` SHA256: `1c121b7b8bf561acde97166ee7fe7c16b68d7dba771d601a0705633b396227a3`.

`PAPER_VI_Preprint1.0_LEAN435_FORMAL_SOURCE_FREEZE.zip` SHA256: `c5c32a9d9315350d8e2683f0c58389824116bd1844f58f7b09ad78d7fe3b61bb`.

## 2. Correspondencia de teoremas


Las letras de los teoremas impresos siguen el orden de lectura del manuscrito. Los identificadores Lean siguientes son los nombres estables del archivo de fuentes suministrado.

| Resultado del manuscrito | Declaración Lean |
|---|---|
| A: fórmula local exacta | `PaperVI.theoremA` |
| B: restricción a triángulos | `PaperVI.theoremC` |
| C: prescripciones exteriores | `PaperVI.theoremB` |
| Proposición 2.1: intervalo de tamaños generales | `PaperVI.cp_window_K4_simple`, con la construcción de orden cuatro en `PaperVI.cp_window_K4` |
| Segundo valor de referencia completo-split | `PaperVI.Research.second_split_baseline` |
| Perturbaciones del segundo núcleo | `PaperVI.Research.second_core_formula` |
| Máximo intrínseco | `PaperVI.Research.cp_eq_max_PhiQ` |
| Reconocimiento por grados | `PaperVI.Research.core_eq_highDegree` |
| D: óptimo de partición excepcional | `PaperVI.Research.ExSetup.theoremE1` |
| D: óptimo fraccional con igualdades | `PaperVI.Research.ExSetup.theoremE1_frac` |
| D: óptimo triangular | `PaperVI.Research.ExSetup.theoremE2` |
| D: brecha de restricción | `PaperVI.Research.ExSetup.theoremE3` |
| Máximo sobre todos los núcleos de la familia excepcional | `PaperVI.Research.ExSetup.theoremE4` |
| Ejemplos concretos de brecha lineal | `PaperVI.Research.exModel_linear_gap` |
| Conservación de un levantamiento físico parcial | `PaperVI.Research.theoremB_extending` |
| Cambio del levantamiento exterior | `PaperVI.Research.theoremB_recourse` |
| E: conteo para una prescripción | `PaperVI.Research.prescribed_count` |
| E: cotas inferior y superior totales | `PaperVI.Research.theoremN` |
| Lema 10.1: compensación exacta | `PaperVIRecourse.used_add_resid_eq` |
| Lema 10.1: prefijo legal arbitrario | `PaperVIRecourse.exists_optimal_partition_extending_prefix` |
| Prefijo físico de triángulos compatibles | `PaperVIRecourse.exists_optimal_partition_of_compatible_triangles` |
| Proposición 10.2: cambio completo 34k/68k | `PaperVIRecourse.exists_full_allK5_recourse` |
| Recuentos terminales óptimos | `PaperVIRecourse.optimal_allK5_counts` |
| Reparación protegida del levantamiento | `PaperVIRecourse.protected_allK5_step` |
| Primera fase de conectividad | `PaperVIRecourse.lift_alignment` |
| Segunda fase: pasos de distancia 18 | `PaperVIRecourse.terminal_alignment_missing_bound`, `PaperVIRecourse.terminal_alignment` |
| Teorema 10.3: conectividad restringida | `PaperVIRecourse.restricted_allK5_connectivity` |
| Identidad del valor de referencia equilibrado y óptimo split sin modificaciones | `PaperVI.Mval_eq`, `PaperVI.cp_refGraph_eq_Mval` |
| Certificado universal de bipartición y cota inferior | `PaperVI.slack_identity`, `PaperVI.slack_nonneg`, `PaperVI.cp_ge` |
| Empaquetamiento triangular: óptimos integral y fraccional real | `PaperVI.triangle_packing_eq` |
| Lema 6.1: rigidez del núcleo cordal | `PaperVI.core_complete_of_chordal` |
| Fórmula cordal y estabilidad bilateral por ediciones | `PaperVI.cp_chordal`, `PaperVI.chordal_stability` |
| Óptimo de partición fraccional real | `PaperVI.fractional_eq_cp`, `PaperVI.frac_slack_identity` |
| Óptimos integral y fraccional de ganancia | `PaperVI.gain_eq` |
| Tipos de todos los óptimos integrales y fraccionales | `PaperVI.optimal_types`, `PaperVI.frac_optimal_support` |
| Obstrucción excepcional de estrella parcial | `PaperVI.Research.ExSetup.partial_star_obstruction` |
| Apéndice A: fórmula elemental de join completo con p≥24Δ(H) | `PaperVI.theoremA1` |
| Apéndice B: localización de bloques ineficientes en a lo sumo 21t aristas | `PaperVI.inefficient_edges_le`, mediante `PaperVI.choose_two_le_21_slack` |
| Prescripciones óptimas distintas | `PaperVI.two_pow_m_optimal` |

El mapa del complemento cubre 39 grupos de resultados del manuscrito. `COMPLETE_THEOREM_MAP.json` identifica sus módulos fuente y la ubicación de las declaraciones; `SOURCE_IMPORT_DECLARATION_MAP.json` cubre cada módulo de la clausura importada. El intervalo local de A y B es p≥18h+1 (p≥18h en el caso equilibrado); C usa p≥63h. La Proposición 2.1 tiene las desigualdades de tamaños generales enunciadas por separado.

Todas las conclusiones de partición conciernen a particiones reales en cliques de G. El caso excepcional especifica un clique P, un conjunto independiente R, adyacencia completa entre ellos y un vértice adicional z con el vecindario indicado. No es simplemente un modelo entero con un número de partición supuesto.


## 3. Alcance exacto de las conclusiones formalizadas


El Teorema D y el ejemplo de estrella parcial de la Sección 8.3 exigen `|R| ≥ |P|+2`, equivalentemente `q ≥ p+3`; su formulación con tamaños sin restricción permite p=0 y conjuntos de vecinos vacíos. La comparación del máximo sobre los núcleos exige `q=2p` y `p≥19`. La familia concreta de brecha lineal toma `p=3t`, `t≥7`.

El reconocimiento por grados bajo A supone n≥3. Identifica la referencia que satisface el teorema local, pero no afirma que el máximo intrínseco tenga un único maximizador. No se afirma un teorema de unicidad del maximizador intrínseco.

La Proposición 9.1 está condicionada al invariante real del levantamiento: aristas legales, pares utilizados del núcleo disjuntos, conjuntos del núcleo disjuntos para aristas exteriores incidentes, cardinalidades prescritas y carga acotada. En su contexto mixto general, la completación terminal puede cambiar globalmente. Trece cuenta asignaciones exteriores, no bloques de la partición completa.

La Sección 10 supone un join completo y todos los bloques exteriores de orden cinco. La Proposición 10.2 supone dos levantamientos completos ya legales y q≥2p−1; no tiene hipótesis de carga pequeña ni cota superior sobre q. Lean utiliza cotas finitas arbitrarias de carga para estos levantamientos, sin exigir una cota uniforme en términos de h. Su conclusión sobre la familia conservada es física: se conservan los triángulos terminales antiguos que no comparten aristas con el nuevo levantamiento. Las cotas 34k/68k se aplican a las familias completas de bloques dados por conjuntos de vértices, y no simplemente a una distancia abstracta de coloreos.

El Teorema 10.3 exige además 2p−1≤q≤2p+1, p≥63h y carga≤7h tanto en los dos estados extremos como en todo el camino. En un join completo, h=editDegree=Δ(H). `BlockPath` registra particiones reales en cada estado y diferencia simétrica de bloques en cada paso. La inducción protege primero las asignaciones exteriores ya alineadas con el objetivo y después los triángulos terminales compartidos con el objetivo. Esta es una conectividad restringida; los óptimos mixtos K4/K5 y los óptimos con levantamientos solo de K5 sin cota de carga quedan fuera de su conclusión. El punto de entrada más fuerte de la fase terminal acota el número de pasos por el número de triángulos terminales objetivo ausentes del estado inicial. No se afirma optimalidad ni una cota de tiempo de ejecución para estas constantes de modificación y de caminos.

El Teorema E cuenta familias etiquetadas de conjuntos de vértices, no listas ordenadas ni clases de isomorfismo. El enunciado formal proporciona las cotas finitas explícitas, incluido el piso del exponente inferior. La asíntota logarítmica elemental se deduce en el manuscrito; no es una premisa formal separada.

Las particiones fraccionales tienen igualdad en cada arista y pesos reales no negativos. Esto no es cobertura fraccional con desigualdades ni integralidad de todo el politopo para objetivos arbitrarios. El óptimo fraccional de empaquetamiento de triángulos también se toma sobre el modelo real canónico.


## 4. Dependencias demostradas, compilación y auditoría de axiomas

Häggkvist–Janssen y Vizing ordinario son dependencias demostradas en la clausura de imports suministrada; no son axiomas matemáticos supuestos. El primero aporta la completación residual mediante coloreo de aristas con listas. El segundo aporta el paso de conteo. Las formalizaciones registradas por el autor son Häggkvist–Janssen, Palomar `PALOMAR-2026-10-15-000003`, versión 1, repositorio `jtraverso/haggkvist-janssen`, commit `807e08bd7c480d4fae80c1b78377d23989d39ab0`; y Vizing, Palomar `PALOMAR-2026-10-15-000004`, versión 1, repositorio `jtraverso/vizing`, commit `01c72ed7efde2353a4bb1654f69b5c0bc5038863`. El registro documenta la procedencia; la compilación local final y la auditoría transitiva de axiomas establecen el estado de las dependencias efectivamente importadas. No se infiere una completación equitativa con listas a partir de Vizing ordinario.

La compilación del agregado de Preprint 1.0 y el control separado de enunciados terminan con código cero. El control examina 32 tipos exportados y sus dependencias axiomáticas. La auditoría de todas las declaraciones examina 1836 declaraciones locales en 79 módulos y visita transitivamente 3421 declaraciones, sin axiomas no estándar. Su unión axiomática es exactamente `propext`, `Classical.choice` y `Quot.sound`. Cada módulo enumerado debe estar presente en el entorno importado; la ausencia de un módulo hace fallar la auditoría. Un mapa separado relaciona archivos fuente, imports reales y recuentos de declaraciones. El análisis de fuentes activas, enmascarando comentarios y cadenas, no encuentra `sorry`, `admit`, declaraciones `axiom` del proyecto ni escapes `native_decide`, `implemented_by` o `extern`.

La compilación utilizó la caché fijada de Mathlib y resultados locales compatibles de compilación. Lake recompiló las fuentes con nuevas cabeceras de licencia y los imports afectados. Los controles finales se ejecutaron contra ese agregado. No fue una reconstrucción sin caché. Los registros conservan advertencias de obsolescencia y de linter heredadas; no se afirma ausencia de advertencias. Los registros autoritativos son `BUILD_PUBLIC_1_0.portable.log`, `ENDPOINTS_PUBLIC_1_0.portable.log` y `FULL_AUDIT_PUBLIC_1_0.portable.log`, cada uno con su código de salida cero registrado. El manifiesto de fuentes y el recibo de freeze vinculan estos registros a las fuentes finales.

## 5. Reproducción de los controles formales

Extraiga `formal_sources/PAPER_VI_Preprint1.0_LEAN435_FORMAL_SOURCE_FREEZE.zip` en una carpeta nueva, instale su toolchain Lean fijado y ejecute lo siguiente desde la raíz de ese proyecto. El archivo contiene todas las fuentes locales y su configuración, sin caché `.lake` ni junction dependiente de la máquina.

```
lake exe cache get
lake build PaperVIRelease
lake env lean -j1 -s32768 EndpointGate.lean
lake env lean -j1 -s32768 FreezeFullAudit.lean
```

Conserve sin cambios el `lake-manifest.json` suministrado. El comando de caché obtiene archivos compatibles con esas dependencias fijadas; no elimine ni actualice el manifiesto para seleccionar versiones de dependencias. Compilar un único módulo intermedio no sustituye la compilación del agregado canónico y sus dos controles finales.

## 6. Certificados finitos y regresiones adversariales

El paquete de certificados finitos de `03_reproducibility/` contiene 33 certificados de grafos explícitos: 18 casos locales A–C y 15 casos excepcionales. Los casos locales incluyen el umbral equilibrado p = 18h, el general p = 18h + 1, los tres tamaños exteriores permitidos, eliminaciones simultáneas en el núcleo y entre las partes junto con adiciones exteriores, estrellas concentradas de grado dos, un ciclo exterior y prescripciones mixtas K4/K5 en p = 63h. Los casos excepcionales usan p = 2, q = 5, todos los valores a = 0,1,2 y b = 0,1,2,3,4; incluyen vecindarios vacíos y el caso a = 2, b = 1 que utiliza K4.

El generador usa una heurística finita de completación voraz; no implementa la demostración universal de Häggkvist–Janssen. Un comprobador independiente no importa código del generador. Reconstruye cada clique y la multiplicidad de cada arista, comprueba tipos, prescripciones y recuentos exactos, y verifica cotas duales con signo para el objetivo excepcional de partición fraccional. También comprueba particiones triangulares reales frente a duales no negativos de cobertura de triángulos. Estas igualdades primal–dual finitas certifican los ejemplos; los resultados universales tienen sus demostraciones escritas y en Lean por separado.

Certo genera y verifica de nuevo seis certificados de cobertura exacta frente a sus especificaciones exactas: un caso A con tres clases de modificación, uno triangular con estrellas concentradas, dos de prescripción en el umbral y dos excepcionales. El resultado de cobertura exacta de Certo verifica la partición suministrada; la optimalidad global de esos casos finitos se justifica por separado mediante el dual entero comprobado. Se rechazan tres alteraciones independientes: cobertura incompleta, cobertura repetida y prescripción incorrecta. Un cuarto control de Certo cambia la identidad de la especificación y es rechazado por la comprobación de procedencia. Ese rechazo no se presenta como rechazo de solver ni como contraejemplo matemático.

Un ejemplo separado de join completo con dos aristas exteriores tiene tres estados óptimos reales. Se protege un levantamiento K5 mientras cambia el otro. El comprobador confirma 1938 triángulos terminales compatibles conservados, 24 bloques anteriores perdidos, diferencia simétrica 48 y un recoloreo terminal final de distancia 6. Todos los estados pertenecen a la clase all-K5 con carga acotada indicada; el camino de dos pasos respeta la cota finita 1949 y la cota uniforme por paso 884. Se rechazan cotas de distancia y carga indebidamente reducidas como controles negativos. Tres certificados adicionales de Certo validan la cobertura exacta de aristas en cada estado suministrado. Las distancias del camino, la preservación y la pertenencia a la clase de carga acotada se comprueban independientemente. Es un ejemplo finito de camino, no un cálculo exhaustivo de conectividad.

Ejecute lo siguiente desde `03_reproducibility/`. Los comprobadores independientes de Python usan sólo la biblioteca estándar. La verificación con Certo requiere además la instalación de Certo registrada. Los certificados suministrados conservan la identidad de su especificación; la regeneración crea certificados para las rutas locales de las especificaciones.

```
python generate_v06.py
python verify_v06.py
python recourse_v06.py
python verify_recourse_v06.py
python run_certo_v06.py
python run_certo_recourse_v06.py
```

Ningún censo finito es premisa de demostración de un teorema universal. Los scripts suministrados y los certificados comprobados independientemente respaldan sólo sus casos finitos indicados.

## 7. Alcance matemático y bibliográfico

El paquete de fuentes demuestra los enunciados formalizados con sus hipótesis explícitas. No establece prioridad histórica ni sustituye la revisión matemática independiente. La comparación dirigida incluye cotejos completos de EFO, CEO, la galerada de autor de EOZ, las cotas de Ma para grafos de umbral, la enumeración de grafos línea de McGuinness–Rees y la caracterización de joins con factor independiente de Wallis–Zhang. La Proposición 3.2 y el Corolario 3.3 de Wallis–Zhang incluyen el caso de frontera del Teorema D en el cual el vértice excepcional es adyacente a todos los vértices del exterior ordinario.

El resultado pertinente de Pullman–Donald se atribuye mediante el artículo de EFO cotejado (p. 94) y Wallis–Zhang (Corolario 3.3); su artículo original no estuvo disponible para inspección directa. Wallis–Wu91 se compara mediante su resumen primario y el anuncio de los autores. Estas limitaciones impiden afirmar una investigación exhaustiva de prioridad histórica. El Lema 4.2 de Okechukwu aporta una cota superior de partición triangular bajo sus propias hipótesis de coloreo, capacidad y defectos; el solapamiento con el Teorema B se afirma sólo en los subcasos que cumplen esas hipótesis y no en todo el intervalo de modificaciones locales.

Paper IV demuestra la cota exacta para grafos cordales suficientemente grandes, junto con una cota para todos los órdenes con una constante aditiva absoluta. Paper VI estudia fórmulas exactas y estructura adicional bajo sus propias hipótesis. La nota separada de aplicación IV–VI tiene su propio punto de entrada y validación; este paquete de fuentes no certifica la clausura de fuentes de esa nota. La conectividad de bloques mixtos K4/K5 arbitrarios y la conectividad sin cota de carga quedan fuera de la Sección 10.
