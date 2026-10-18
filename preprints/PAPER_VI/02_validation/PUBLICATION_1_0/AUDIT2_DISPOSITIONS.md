# Paper VI — audit2 dispositions for Preprint 1.0

Only the findings actually supplied to this revision are addressed. The complete 26-item report was not available; no statement that all 26 items are closed is made.

## VI-01: Missing size hypothesis in Section 8.3

**CORRECTED.** Repeated q≥p+3 from Theorem D and restricted the displayed balanced specialization q=2p to p≥3. Existing ExSetup.partial_star_obstruction requires |R|≥|P|+2, exactly the same condition. No theorem was extended.

## VI-02: Undefined legal core set in Proposition 9.1

**CORRECTED.** Defined N⊆P to induce a clique and to be fully adjacent to the two endpoints of the chosen exterior edge. Compatibility with the old lifting is imposed or repaired separately. This matches LegalNewBlock in PhysicalRecourse.lean; size two or three is the separate proposition assumption.

## VI-03: Attribute an exact all-orders Erdős81 bound to IV

**REJECTED_WITH_PRIMARY_EVIDENCE.** The official Paper IV README and Preprint v1.23 state the sharp bound eventually, and M(n)+b for all orders with an absolute b. They explicitly disclaim universal b=0. The existing eventual attribution is retained; the companion spells out both scopes. The reviewer suggestion would strengthen IV without proof.

## VI-04: Okechukwu Lemma 4.2 comparison too broad

**NARROWED.** The main text and companion retain its own coloring, capacity and defect hypotheses. Equality with the elementary triangle lower bound is asserted only for the matching clean-crossing subcases, not for the full simultaneous-edit window.

## VI-05: Paper V reference lacks an identifier

**CORRECTED.** Reference [V] now identifies Preprint 1.0 and its public repository directory; no DOI is invented.

## VI-06: Companion theorem map incomplete

**CORRECTED.** Expanded from 27 to 39 result groups, covering the universal certificate, integral and real fractional optima, chordal rigidity/formula/stability, efficient support, exceptional obstruction, both appendices and distinct prescriptions, in addition to all earlier main results. Every listed declaration was located in the supplied source.

## VI-07: Draft/internal-process labels in publication documents

**CORRECTED.** All four semantic documents and front matter use Preprint 1.0. Removed private-review and internal-gate narrative; retained mathematical limits and measured build facts. Earlier sealed records remain immutable and are not publication text.

## VI-08: Public formalization link and portable evidence

**CORRECTED_IN_CURRENT_PACKAGE.** Canonical public directory is preprints/PAPER_VI/05_formalization. The new source archive contains pinned portable configuration, local sources, licenses, relative manifests and portable logs, with no .lake cache or machine-specific junction. Historical sealed records are not rewritten.

## VI-09: Copyright and Apache headers in own Lean sources

**CORRECTED.** Own sources now carry copyright 2026 Juan Pablo Traverso Gianini and SPDX-License-Identifier:Apache-2.0. Existing credits and notices are preserved. Active theorem/proof text is checked identical to the previous source snapshot. A new aggregate and type/axiom checks bind this new licensed source archive.

## VI-10: HJ and Vizing might be assumptions rather than proved imports

**VERIFIED_PROVED_DEPENDENCIES.** Inspected HJ polynomial-certificate/Combinatorial-Nullstellensatz proof and Vizing finite partial-edge-coloring/fan/Kempe proof. The wrappers invoke proved theorems. The canonical full-closure axiom check is recorded separately; ordinary Vizing does not supply equitable list completion.

## VI-11: All26 reviewer findings closed

**NOT_CLAIMED.** The full 26-item audit report was not available. This disposition covers only the concrete findings supplied to the revision. It must not be presented as closure of an unseen full report.

## Evidence for the IV scope

The official repository README states the eventual sharp bound and an all-orders additive bound, explicitly excluding a universal claim b=0. See [Paper IV public repository](https://github.com/jtraverso/erdos-81-chordal-clique-partitions) and its [archived I–IV snapshot](https://doi.org/10.5281/zenodo.23089131). The revision retains this scope.

## Boundary of this release

No new mathematical theorem, stronger range, new proof axiom, or priority guarantee is introduced. The formula, recourse and connectivity statements retain their previously encoded hypotheses. The explicit size condition in Section 8.3 restores a standing hypothesis already required by its formal theorem.
