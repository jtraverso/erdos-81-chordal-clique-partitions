# Response to the supplied external feedback

Juan Pablo Traverso Gianini · Preprint 1.0 · 18 October 2026

This response addresses the concrete observations supplied with the reviews of
the previous review snapshot and records the disposition of suggestions. The four
separately named detailed `AUDIT2_*.md` reports were not available in the supplied
files; this report does not claim to close unseen line-specific observations.
The current documents also underwent a new internal review. Review, Lean kernel
checking, finite computation and historical-priority assessment have distinct scopes.

## Common observations

| Observation | Disposition in Preprint 1.0 |
|---|---|
| Draft labels and internal-process wording in current documents | Current English and Spanish manuscripts and companions use Preprint 1.0 throughout. Markdown, TeX and PDF are checked separately; historical third-party titles are not retrospectively renamed. |
| Public identifiers and inaccessible series references | Papers I–IV cite the deposited edition DOI 10.5281/zenodo.23089131. The new works and formalization packages have separate locations in the official public series repository. |
| Personal workstation paths in evidence | Public source packages contain relative paths. Current Certo certificates were regenerated from a neutral working directory and verified; their certificate content was not edited for redaction. Portable transcript copies and relocation records distinguish metadata redaction from mathematical checking. |
| Missing software license and copyright | Full Apache-2.0 grants, copyright attribution and source ownership records accompany the author's Lean/software sources. Existing upstream notices remain. Documents use CC BY-NC 4.0. The notes include the LICENSE files to which their instructions refer. |
| Formalization described as a work history | The separate companions describe final entry points, pinned dependencies, theorem correspondences, source archives, measured checks and reproduction. The principal manuscripts retain only a short formalization paragraph. |
| Artificial-intelligence declaration | The established Paper IV declaration is carried consistently into the main documents; the companions describe the relevant computational and formal scope. No AI system is an author and no human peer review is asserted. |

## Paper V

| Observation | Disposition |
|---|---|
| Attribution of Erdős 81 and outdated consultation wording | The context cites the problem page, Paper IV and Okechukwu's stated results. No priority is claimed for the already established bound. An unsupported access-date claim is removed. |
| Theorem 6.2 formal interface weaker than the written claim | The new copy-packing interface constructs the mapped multiset from specified feasible copied packings, proves its cardinality identity, and supplies the integral-transfer and optimal-packing adapters. |
| Theorem 7.3 mapping weaker than the written claim | The correspondence uses `PaperV.mixed_copy_integral` for the actual mixed-copy conclusion. |
| Missing supplementary material and reproducibility | The delivered formal companion contains the supporting-results map; unsupported references to an undelivered separate supplement are removed. SEAL scripts, variants, outputs, rational certificates and independent checks are included under `03_reproducibility/SEAL`. The BK certificates and their independent checker are also included. |
| Multiple files labeled v1.10 | There is one current Preprint 1.0 manuscript pair and one current companion pair. Earlier private editorial alternatives are not current publication artifacts. |
| N1 implementation issue | The first public implementation uses the corrected atomic relocation/insertion rule. The final code and regenerated evidence are described by their behavior and measured scope. |

## Paper VI

| Observation | Disposition |
|---|---|
| Missing size hypothesis in §8.3 | The exceptional setup explicitly retains `q ≥ p+3`; the linear-gap specialization keeps its stronger size assumptions. |
| Undefined legal core set | A legal core set is defined by core membership, its clique property and adjacency to both exterior endpoints. Compatibility with other assignments is handled by the lifting invariant and recourse argument. |
| Citation of V and incomplete formal map | The public series reference and the complete result-to-declaration correspondence are supplied. The companion covers 39 result groups, including fractional, exceptional, appendix and recourse statements. |
| Ambiguous classical Lean dependencies | Häggkvist–Janssen and ordinary Vizing are explicitly proved dependencies in the supplied source closure, with provenance and transitive axiom checks. Registration alone is not offered as proof of a build. |
| Okechukwu Lemma 4.2 overstated | The comparison is limited to that lemma's actual coloring, capacity and defect hypotheses. It is not described as the complete simultaneous-edit theorem here. |
| Thirteen assignments versus whole-partition distance | The local lifting recourse statement is distinguished from global mixed connectivity. The complete-join all-K5 whole-partition result has its separate hypotheses and constants. |
| Theorem lettering and existence versus all-optima wording | Printed letters follow reading order; stable Lean identifiers are mapped explicitly. The construction claims existence of a specified optimal partition, without excluding K5 optima. |

## Note I

| Observation | Disposition |
|---|---|
| First-entry and related work insufficiently attributed | The abstract and structural-input discussion credit the relevant earlier sources and distinguish IV's selected localization proof from the transfer interface. |
| Input 3.1 presented as stronger than the established rounding theorem | It is identified as Rohatgi–Urschel–Wellens, Theorem 3.4 with r=4; IV supplies the formal implementation used by the note. |
| Inputs lack precise locations | The note identifies the relevant numbered results of IV and the physical-witness budget used in the assembly. |
| Suggestion to merge with V | Not adopted: the agreed scope keeps this attributed application in a separate manuscript and independent Lean project. It does not claim a new independent solution of Erdős 81. |

## Note II

| Observation | Disposition |
|---|---|
| Structural inputs lack theorem numbers | Exact locations in IV are supplied, including the construction and defect-budget identity. |
| Integer step B ≤ M omitted | The proof states integrality and the two possible values of Q−M: 1/24 and 9/24 according to the order modulo three. |
| A unique maximizing size implied | The text says a maximizing size; it allows the two maximizers in the appropriate residue class. |
| Optional improvement from 24d+25 to 24d+9 | The stronger intermediate estimate is explained by the residue calculation, but the established weaker theorem bound is retained. No unnecessary scope change is made. |

## A correction to the review's requested scope change

The statement that Paper IV proves the sharp integer bound with no additive term
at every order is not supported by its published theorem. IV proves an all-order
bound `c4(G) ≤ M(n)+b` for an absolute constant b and the sharp bound `M(n)` for
sufficiently large orders. This already gives the `n²/6+O(n)` conclusion of Erdős 81.
Preprint 1.0 preserves that distinction. The stronger assertion `b=0` at every
order has not been inserted.

## Evidence

Per-work validation directories contain the source receipts, portable build and
axiom-audit evidence, semantic comparison and rendering records. The aggregate
static report and manifest verifier are in this directory. An internal PASS is
limited to these documented checks; it is not a claim of independent human peer
review or an exhaustive historical-priority search.
