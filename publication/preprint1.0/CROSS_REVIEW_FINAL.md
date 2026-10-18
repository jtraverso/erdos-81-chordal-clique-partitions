# Revisión cruzada final — Preprint 1.0

**Resultado: PASS de contenido; comprobación de ensamblaje pendiente para los archivos aún en integración.**

## Alcance y evidencia

Revisión independiente de los manuscritos principales de Papers V y VI, en inglés y español, contrastando sus afirmaciones de formalización con los companions Markdown disponibles. Se revisaron además el README y el HTML de presentación de la serie y de sus cuatro nuevas entregas. La lectura dirigida cubrió resúmenes, hipótesis y alcance de los resultados, atribuciones, aplicaciones IV–V, SEAL, excepciones, recourse, conectividad restringida, formalización y referencias pertinentes. Los hashes siguientes fijan los documentos leídos.

Esta revisión no ejecutó Lean, programas experimentales ni navegadores; tampoco es una inspección visual de los PDF o una nueva prueba de todos los resultados matemáticos. La fidelidad EN/ES se contrastó mediante lectura semántica de las secciones críticas y extracción de todos los fragmentos matemáticos con Pandoc. El estado de compilación y los recuentos de auditoría se contrastaron como declaraciones documentales, sin repetir los controles formales. Los companions que terminan de compilar no se consideran ausentes por esa circunstancia temporal.

## Resultado por ámbito

- **Paper V.** Las hipótesis de certificado y realizador permanecen explícitas. La aplicación cordal conserva los constructores y la localización de IV; no presenta el transfer engine como sustituto que demuestre por sí solo su coste de realización. Se distingue la cota M(n)+b para todo orden de M(n) para órdenes suficientemente grandes. Okechukwu recibe atribución explícita y no se reivindica prioridad para esas conclusiones extremales. El paso de redondeo asintótico no se atribuye a los teoremas generales de V; la aplicación independiente de la nota conserva sus dependencias IV/RUW.
- **SEAL.** Las afirmaciones del principal sobre N1/N2 se refieren a las operaciones matemáticas y a la búsqueda exhaustiva de profundidad fija bajo mejora estricta. La complejidad excluye el cálculo opcional de la cota LP. El companion distingue la implementación BASE/v3 de N1 de la referencia con N1/N2, la comprobación de una asignación propia de una implementación general de BKW, y los certificados finitos de una verificación integral del software. No se afirma optimalidad general por detenerse en un óptimo local.
- **Paper VI.** A–C conservan la región local y las condiciones numéricas; el enunciado de A afirma existencia de un óptimo con esos tipos, no que todos tengan esa forma. El caso excepcional conserva q≥p+3. La fórmula intrínseca no afirma unicidad del núcleo maximizador. El conteo se enuncia bajo C y p≥16. La modificación de trece asignaciones sigue limitada a la capa de levantamiento.
- **Conectividad de VI.** El principal y el companion mantienen join completo, bloques exteriores K5 y carga acotada en el teorema de conectividad. El recourse 34k/68k requiere dos levantamientos completos legales y q≥2p−1; no se introduce una afirmación para prescripciones mixtas o perturbaciones arbitrarias del grafo. Las cotas 884 y 18 conservan su ámbito específico.
- **Antecedentes y formalización.** Las comparaciones con EFO, PD81 a través de las fuentes consultadas, Wallis–Zhang y Okechukwu están acotadas. La continuación de IV se presenta como posterior a su cota ya demostrada. Los principales no contienen una afirmación de formalización más fuerte que las limitaciones explícitas de los companions revisados. Las dependencias HJ/Vizing se distinguen de axiomas admitidos. No encontré una etiqueta activa de borrador, un estado PENDING/TODO ni una ruta privada en los principales.

## Paridad entre idiomas

| Documento | Fragmentos matemáticos EN | ES | Resultado |
|---|---:|---:|---|
| Paper V | 701 | 701 | Multiconjuntos idénticos tras las tres traducciones naturales de texto dentro de fórmulas: “for every”, “feasible”, “is a maximum packing”. |
| Paper VI | 679 | 679 | Una única diferencia textual: `\text{if }` / `\text{si }`; todos los símbolos matemáticos permanecen idénticos. |

Ambos principales carecen de bloques de código y de fragmentos de código en línea que comparar. La igualdad de fragmentos matemáticos no sustituye la lectura de cuantificadores y negaciones en prosa; esas condiciones se contrastaron en los ámbitos enumerados antes. No se detectó un cambio de alcance entre EN y ES.

## Hallazgo corregido y enlaces

**WEB-NOTE-II-01 — cerrado.** El resumen de nivel 2 de la página HTML de Nota II inicialmente omitía “n suficientemente grande” y la no negatividad del déficit. La versión actual, revisada en EN y ES, define d=M(n)−cp(G) y exige explícitamente n suficientemente grande y 0≤d≤n/2000. No se cambió el manuscrito.

Los seis recursos gráficos enlazados por los Markdown de V existen en staging. La inspección estática de enlaces relativos de los doce README/HTML encuentra únicamente destinos todavía pendientes de ensamblar: el directorio formal y los dos PDF companion de V, y los directorios de integridad de V y VI. Sus nombres son coherentes con las rutas canónicas previstas. **El ensamblador debe repetir la comprobación de existencia después de copiarlos y antes de publicar.** No se consideran hallazgos bibliográficos ni defectos de los documentos; tampoco se afirma que esos enlaces ya funcionen. No se comprobaron respuestas HTTP ni el renderizado de HTML.

La observación de `preprints/README.md` que excluye “unrelated working drafts” describe el alcance del repositorio y no etiqueta las nuevas entregas como borradores.

## Inventario de hashes

Los caminos `PAPER_V/` y `PAPER_VI/` se refieren al staging de Preprint 1.0; el prefijo `public-repo/` identifica la copia de publicación. El inventario es portable y no contiene rutas del equipo.

| Archivo | SHA-256 |
|---|---|
| `PAPER_V/01_manuscript/PAPER_V_preprint_v1.0_en.md` | `b94189f78c5291af48625cb2aa9bdbd8b5e48199acb9ba06e476246b2f6183c2` |
| `PAPER_V/01_manuscript/PAPER_V_preprint_v1.0_es.md` | `bbc913b78670f9425dfd01f30db32d7dc8988945cb3e4feee2ca74ef3f235a86` |
| `PAPER_V/05_formalization/FORMALIZATION_COMPANION_v1.0_en.md` | `b75f46f4c2e08ba887b24d9d3b1d61b6d52408a6473804bea299df090b376994` |
| `PAPER_V/05_formalization/FORMALIZATION_COMPANION_v1.0_es.md` | `de385000ad75e429daf716d77b3bc23acb7d1901c4e12493f2f9035f43d8b1f3` |
| `PAPER_VI/01_manuscript/PAPER_VI_preprint_v1.0_en.md` | `86305a1141f80ee47ff9875015c62e61c0b0919e8aabcfc91c1db3c5f98f83b4` |
| `PAPER_VI/01_manuscript/PAPER_VI_preprint_v1.0_es.md` | `8f5e023ef9b14be0844d2b6435319c1df06715b5e34cad639be44d379db097f1` |
| `PAPER_VI/05_formalization/FORMALIZATION_COMPANION_v1.0_en.md` | `42602f0b230d9a27690005577db4f3461085e3a0cd884851421149ff51013103` |
| `PAPER_VI/05_formalization/FORMALIZATION_COMPANION_v1.0_es.md` | `eb3412de434639f207f5a8156d3714ea5a81304b8f16967a9d933f121c061c13` |
| `public-repo/README.md` | `b12a0400530c19b4462af700c6edc34eb2594390ce71b8f4489c5b34e758976e` |
| `public-repo/index.html` | `7699d74568d6275b525a76bb0ab979fb46430dfd2807cd3aba091f734dc6815b` |
| `public-repo/preprints/README.md` | `e07e1ea40ad0268604e8b57938e177ca21ae09ba7d60fc6170fb41e331e70106` |
| `public-repo/series_notes/README.md` | `ddbc8fefb291e0938b4dfc03663a26f2020bca4516a5d8e81f95eb7c04c10762` |
| `public-repo/preprints/PAPER_V/README.md` | `750f51a185d3404cc8747898243b3de31db4912186fb116ac2c9ee2c5a4a7bf6` |
| `public-repo/preprints/PAPER_V/index.html` | `875f1a493dd53260cff982344a2d55f0947eb0bf6b3972725ec9d243bf8c2766` |
| `public-repo/preprints/PAPER_VI/README.md` | `8c348cb1210e0240def144edb30a75bf47f658a9be0238a9ebb3bdf26e2b94b0` |
| `public-repo/preprints/PAPER_VI/index.html` | `69cd78dbc837b53a7dfbe9daaf343735a686f9d586ec294daf0aa04038113dc7` |
| `public-repo/series_notes/NOTE_I_ERDOS81_TRANSFER/README.md` | `3a206492590972bdb6fa8bf8b4d9bcfddf06afed623cf8c3b4db78cfe6e0efad` |
| `public-repo/series_notes/NOTE_I_ERDOS81_TRANSFER/index.html` | `38b5df55ece5240018fcc4f5d9122067727f26cbb8b61df21ac7d44e4794b8a1` |
| `public-repo/series_notes/NOTE_II_CHORDAL_STABILITY/README.md` | `953dc9617be62bda37127037d621f4bcbf5c587580640ae26f3bb257f5106f69` |
| `public-repo/series_notes/NOTE_II_CHORDAL_STABILITY/index.html` | `248b123aecb9782d3653ec769ff38930927e0d1fdc34f3fc611dce27ce320476` |

El fichero `CROSS_REVIEW_FINAL_DATA.json` conserva los recuentos, la diferencia textual autorizada, los enlaces pendientes y el cierre del hallazgo. No se modificó ningún manuscrito, página de publicación ni fuente Lean durante esta revisión.
