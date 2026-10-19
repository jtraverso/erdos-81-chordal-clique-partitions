# Final internal editorial audit — Paper IV v1.24

**Verdict: EDITORIALLY_READY — PASS.** Date: 19 October 2026. No open corrective actions in the editorial scope.

This is an AI-assisted internal editorial review by Codex, not an independent external or human review. It preserves and cites the earlier mathematical/formal audit rather than relabeling it as a fresh audit of v1.24. Publication-stage navigation and deposit receipts are checked separately after upload.

| Gate | Result | Evidence and scope |
|---|---|---|
| E0 | PASS | Baseline `ef31294ad67dfe3f44bc47cec4791c836f55e8aa`; author-authorized editorial publication; no Lean/Lake execution |
| E1 | PASS | 237 original displayed equations in each language retain their order and mathematical content; two terminal punctuation signs per language moved outside boxes; one already-existing premise expanded in F.5; all equation labels and 33 named result headings retained |
| E2 | PASS | Article: 2,213 mathematical fragments per language with identical normalized multisets; companion: 18 per language; translated placement of one inline z differs in prose order only |
| E3 | PASS | Original bibliographic entries and attribution retained; [23] points to the relocated discussion; [24] identifies the companion; only the obsolete draft-status sentence is removed from the IA disclosure |
| E4 | PASS | 607 Lean files byte-identical to the frozen ZIP; unchanged separate annex hash; 19 recorded successful targets, 461 axiom outputs within the standard set, 224 export checks; historical evidence only |
| E5 | PASS | Four final PDFs compiled from their final TeX; 61/63 article pages and 13/13 companion pages; all 150 pages reviewed in 16 contact sheets; eight selected pages inspected individually; no clipping flags, missing characters, undefined references or overfull boxes |
| E6 | PASS | Papers I–III retain manuscripts and source freezes; updated summaries follow the published abstracts; root describes the mathematical series and notes; prior IV edition and freeze remain linked |
| E7 | PASS | Published new documents contain no machine-private paths; package link and hash results are saved with the release checks |
| E8 | PASS | Article and companion agree on v1.24, date and unchanged freeze; changelog distinguishes editorial changes from the frozen mathematics |

## Review and corrections

The approved local edition had already closed six editorial observations: a threshold referent, punctuation in E1, two source locators, an overbroad automated-check claim, visual-evidence binding and escaped spaces in a URL macro. This publication round rechecks the final artifacts rather than inheriting their old PDF hashes. The release delta also removes local-review status, moves four punctuation signs outside boxes, and makes the companion disclosure description consistent with removing the obsolete draft sentence. Automated manuscript checks returned PASS on this round. Navigation and package checks are iterated independently. This check detected a Windows default-encoding conversion in four navigation/citation files; they were restored from their UTF-8 baseline, transformed with explicit UTF-8 and rechecked before release. No manuscript, PDF or Lean file was affected. A second packaging check exposed Windows long-path handling in the standalone verifier; extended path support resolved it, and all 84 documentary entries passed. Both corrective actions are recorded as closed.

Manual review compared the result statements, proof-role replacements and the critical distinctions: all-orders additive bound versus eventual sharp bound; fixed versus sublinear defect; actual retained root versus optimal-size template; original formal evidence versus new document layout. The proof map retains the two branches and their respective inputs. The companion retains definitions and theorem hypotheses, the source map, foundational axiom scope and the distinction between 461 output records and theorem counts.

Paper I's README now states n²/6+n/2, as its unchanged abstract does; the preceding README used the weaker n²/6+n summary. This corrects the navigation summary, not the theorem. Paper II retains its n≥1 scope. Paper III distinguishes the sharp quadratic coefficient from any claim about an optimal linear coefficient.

## Evidence and limits

- [Automated documentary checks](../20_EVIDENCE/AUTOMATED_CHECKS.json)
- [Frozen identity and historical log hashes](../20_EVIDENCE/FROZEN_IDENTITY.json)
- [Visual bindings](../20_EVIDENCE/RENDER_BINDING.json) and [rendered evidence](../20_EVIDENCE/visual/)
- [Existing premise in F.5](../20_EVIDENCE/EXISTING_PREMISE_EXPANSION.md)
- [Publication delta](../20_EVIDENCE/RELEASE_DELTA.json); full v1.23→v1.24 patches are in the same evidence directory
- [Audit procedure](../00_CONTROL/AUDIT_PLAN.md)
- [Earlier source and audit snapshot](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV)

Mathematical fragment comparisons are editorial invariants, not a proof of semantic equivalence for arbitrary prose. No new bibliography search, new mathematical theorem or Lean kernel execution is claimed. The old reports, manifests and source ZIPs remain immutable. This report covers the four document hashes in AUTOMATED_CHECKS.json; publication receipts and the final release manifest identify their distribution.

## Resumen en español

La revisión editorial interna pasa sin acciones correctivas abiertas en su alcance. Se mantiene la matemática y el congelado Lean; sólo cambian exposición, separación del complemento, puntuación, navegación y metadatos. Se conservaron los antecedentes y las atribuciones. La inspección abarcó las 150 páginas finales y quedó ligada a sus hashes. No se ejecutó Lean/Lake ni se presenta esta revisión asistida por IA como revisión humana externa.
