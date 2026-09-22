# Preprints

This directory contains the official author preprint(s) for the Erdős
Problem #81 research program.

- `PAPER_I/` — *Affine Profile Reduction for Fractional Triangle Packings in
  Split Graphs* (preprint v1.3; supersedes public v1.0).
- `PAPER_II/` — *Complete-Split Extremizers for a Fractional Triangle-Cover
  Functional on Chordal Graphs* (preprint v1.2; supersedes public v1.0).
- `PAPER_III/` — *Linear-Error Clique Partitions of Split Graphs via Structured
  Triangle Packing* (preprint v1.5; first formal public release; resolves the
  split-graph case at the `n²/6 + O(n)` scale).
- `PAPER_IV/` — *Clique partitions of chordal graphs: mixed rounding and
  construction in the critical regime* (**author draft**, revision v0.8;
  bilingual manuscripts, frozen Lean sources and internal audit evidence;
  independent final audit remains pending).

Each preprint package uses the release structure:

```text
01_manuscript/
02_validation/
03_reproducibility/
04_integrity/
05_formalization/
superseded/
```

Each canonical paper directory contains the current public release. Papers I
and II retain their complete preceding public packages under
`superseded/preprint_v1.0/`. Paper III had no preceding formal public release;
its audited unpublished draft is retained and labelled as such. Intermediate
internal drafts are not presented as public releases.

Paper IV is explicitly a draft, not a final release. Only its active v0.8
manuscripts are included; earlier local working versions and research
downloads are excluded. The published histories of Papers I–III are retained.
