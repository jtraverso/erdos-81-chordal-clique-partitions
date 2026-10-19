# Clique partitions and chordal structure — Papers I–VI and series notes

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21273143.svg)](https://doi.org/10.5281/zenodo.21273143)

Juan Pablo Traverso Gianini's series studies how fractional packing bounds become exact graph decompositions, what prevents their realization, and what near equality reveals about a graph and its partitions. Erdős Problem #81 motivates the first part of the series; the later papers develop questions of realizability, local optimality and stability.

La serie estudia cómo transformar cotas fraccionales de empaquetamiento en descomposiciones de grafos, qué obstruye esa realización y qué revela la casi igualdad sobre un grafo y sus particiones. El problema 81 de Erdős motiva la primera parte; los trabajos posteriores desarrollan cuestiones de realizabilidad, optimalidad local y estabilidad.

## The mathematical route / Recorrido matemático

| Work | Main question and contribution | Current edition |
|---|---|---|
| [I — Fractional profiles](preprints/PAPER_I/README.md) | Reduce mixed neighborhood profiles in split graphs to a fixed finite linear program. | v1.4, editorial revision |
| [II — Fractional extremizers](preprints/PAPER_II/README.md) | Identify the exact fractional chordal extremum by admissible copies and complete-split terminal graphs. | v1.3, editorial revision |
| [III — Integral split partitions](preprints/PAPER_III/README.md) | Construct clique partitions with sharp quadratic coefficient and linear error for split graphs. | v1.6, editorial revision |
| [IV — Quantitative stability](preprints/PAPER_IV/README.md) | Obtain chordal and rooted-defect bounds, and control graphs and near-optimal partitions with a common root. | v1.24, editorial revision |
| [V — Colorability and realizability](preprints/PAPER_V/README.md) | Separate conflict colouring from realization in resource-dominated packing relaxations. | Preprint 1.0 |
| [VI — Exact local partitions](preprints/PAPER_VI/README.md) | Determine optimal clique-partition counts under local perturbations, with prescriptions and structural consequences. | Preprint 1.0 |

The connections are mathematical, not a requirement to read every earlier result first. Papers I–II explain fractional profiles and extremal structure; III–IV add integral constructions and stability. Paper V abstracts transfer mechanisms, while VI gives exact local constructions. Each manuscript states its actual inputs and attribution.

Las conexiones no obligan a leer toda la serie antes de abordar un resultado. I–II estudian perfiles fraccionales y estructura extremal; III–IV añaden construcciones integrales y estabilidad. V formula mecanismos de transferencia y VI ofrece construcciones locales exactas. Cada artículo identifica sus dependencias y atribuciones.

## Two connecting notes / Dos notas de conexión

- [Note I — From realizability certificates to the Erdős 81 bound](series_notes/NOTE_I_ERDOS81_TRANSFER/README.md) organizes part of the route of IV through V's transfer framework. It retains the inputs and their attribution, without claiming a new priority result for Erdős #81.
- [Note II — Exact stability for nearly extremal chordal clique partitions](series_notes/NOTE_II_CHORDAL_STABILITY/README.md) combines the structural input of IV with the local formula of VI.

## Read the series / Leer la serie

- [Bilingual HTML guide](index.html) · [Browser preview](https://htmlpreview.github.io/?https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/index.html).
- Each paper page links its English and Spanish PDF, LaTeX and Markdown. All six papers and the two notes have separate formalization companions. Papers I–III now follow the editorial layout of IV; their Lean freezes remain unchanged.
- [Publication index](PUBLICATION_INDEX.json) · [Citation guide](CITATION.md).

## Formal sources and audit evidence / Fuentes formales y evidencias

Papers I v1.4, II v1.3 and III v1.6 are editorial revisions released together. Their individual changelogs, formal companions and internal editorial audits are linked from each paper page. No Lean/Lake rebuild was performed.

The papers have distinct frozen source packages and recorded audit scopes. Paper IV v1.24 changes exposition and document organization; its Lean freeze remains `piv-v12-fb459343d234`. The [editorial changelog](preprints/PAPER_IV/CHANGELOG_v1.24.md), [new internal editorial audit](preprints/PAPER_IV/02_validation/01_INTERNAL_AUDITS/run_v1.24_editorial_release/10_REPORT/FINAL_INTERNAL_AUDIT_REPORT.md) and [unchanged formal sources](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/05_formalization) distinguish the new documents from the existing kernel evidence.

The preprints and documented AI-assisted reviews are not human peer review. Formal checking, written-proof review and bibliographic comparison have different scopes. Each package records those limits; a successful compilation does not establish historical priority.

Los preprints y sus revisiones asistidas por IA no equivalen a revisión humana por pares. La comprobación formal, la revisión de pruebas escritas y la comparación bibliográfica tienen alcances distintos, documentados por cada trabajo.

## Editions, citation and licenses / Ediciones, citas y licencias

The [current 32-PDF collection](https://doi.org/10.5281/zenodo.23478825) contains the revised I–III articles and their separate companions. The [preceding 26-PDF collection](https://doi.org/10.5281/zenodo.23476768) includes Paper IV v1.24 and its formal companion. The [series concept DOI](https://doi.org/10.5281/zenodo.21273143) follows the collection. The preceding [24-PDF collection](https://doi.org/10.5281/zenodo.23459196) and the [I–IV snapshot](https://doi.org/10.5281/zenodo.23089131) remain available. Historical manuscripts, source freezes and their audit evidence are retained; identify the paper and version when citing a result. See [CITATION.bib](CITATION.bib) and [CITATION.cff](CITATION.cff).

Zenodo contains individual PDFs; GitHub carries source and evidence packages. [Deposit procedure and receipts](publication/zenodo/README.md). The [publication index](PUBLICATION_INDEX.json) identifies the deposited collection.

Documents are CC BY-NC 4.0. Software retains its applicable licenses, including the author-owned Apache-2.0 releases of V–VI and the notes and the [specific Paper III source-code grant](LEAN_SOURCE_APACHE_2_0_GRANT.md). See [LICENSE.md](LICENSE.md).

## arXiv endorsement


I am preparing to submit this preprint series to arXiv (math.CO) and, as a first-time submitter, I
need an endorsement. If you are an arXiv author eligible to endorse in math.CO, have looked at
these papers, and found that they add value and are appropriate for the category, you can endorse
me at https://arxiv.org/auth/endorse?x=N8V4R6 (endorsement code `N8V4R6`). An endorsement only confirms that the work is suitable for
the subject area; it is not a review or an approval of its results. Thank you.

*En español:* preparo el envío de esta serie de preprints a arXiv (math.CO) y, como es mi primer
envío, necesito un endorsement. Si eres autor de arXiv habilitado para dar endorsement en math.CO,
revisaste estos trabajos y te parece que aportan y son adecuados para la categoría, puedes dármelo
en https://arxiv.org/auth/endorse?x=N8V4R6 (código `N8V4R6`). El endorsement solo confirma que el trabajo es adecuado para el área;
no es una revisión ni una aprobación de sus resultados. ¡Gracias!
