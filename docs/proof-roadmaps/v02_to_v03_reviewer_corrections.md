# Reviewer corrections from v0.2 to v0.3

**Scope.** This note records the corrections made between `paper_B_chordal_toolkit_technical_draft_v02.tex`, `paper_C_fractional_chordal_technical_draft_v02.tex`, and the new v0.3 technical drafts.

The purpose of v0.3 is not to overstate the proof status. It makes the global fractional assembly more robust and explicitly records the remaining local/certificate work in Paper B.

---

## 1. Summary matrix

| Reviewer / Codex point | Status in v0.2 | v0.3 action | Resulting status |
|---|---|---|---|
| Weighted Heavy-Bag bound | Incorrect for arbitrary weights | Replaced unweighted `M_*` by weighted bag maximum `M_x^*` | Corrected |
| Uniform debits for `s_alpha = 0,1` | Undefined division by `binom(s_alpha,2)` | Added debit-active condition `s_alpha >= 2`; set active debit to zero otherwise | Corrected |
| Multi-core / laminar bookkeeping | Present as ownership convention, too compressed | Added explicit retained-core ownership ledger lemma and proof in Paper C | Clarified / strengthened |
| Terminal classification / promotion completeness | Stated as toolkit interface | Kept conditional on Paper B; flagged thresholds as referee-sensitive | Still needs final Paper B package |
| `L_4` certificate | Claimed as certificate theorem | Added note requiring rational data and exact verifier | Needs reproducible package |
| Core-Fan/Farkas theorem | Imported by Paper C | Added debit-active interface and proof-roadmap warning | Needs final normalization proof |
| Rounding Haxell--Rodl/Yuster | Not part of Paper C | Left to Paper D | Standard external input |

---

## 2. Correction A — Weighted Heavy-Bag Lemma

### Problem in v0.2

The v0.2 statement said, for arbitrary nonnegative weights,

\[
\sum_{\mathcal T_u\cap\mathcal T_v\neq\varnothing}x_ux_v
\le
M_*\sum_vx_v.
\]

This is false when `M_*` is the unweighted maximum bag size. For example, in `K_2`, `M_* = 2`, and weights `x_1=x_2=100` give left side `10000` and right side `400`.

### v0.3 correction

Define

\[
M_x^*
=
\max_t\sum_{v:t\in\mathcal T_v}x_v.
\]

Then the correct bound is

\[
\sum_{uv\in E(G)}x_ux_v
\le
M_x^*\sum_vx_v.
\]

The unweighted statement remains

\[
|E(G)|\le M_*n.
\]

### Proof idea

Use a perfect elimination ordering. For each vertex, its later neighbours form a clique and hence lie in one bag. Their total weighted mass is at most `M_x^*`. Orient edges forward in the elimination order and sum.

---

## 3. Correction B — Guard uniform debits for small subcores

### Problem in v0.2

Paper C defined

\[
z_{\alpha,ij}
=
\frac{T_\alpha}{\binom{s_\alpha}{2}}
\]

for all boundary groups. This is undefined for `s_alpha = 0` or `s_alpha = 1`.

More importantly, when `s_alpha <= 1`, the retained subcore contains no core edge `ij`, so there is no triangle of the form `uij` that can realize a quadratic boundary debit.

### v0.3 correction

Define a boundary group as **debit-active** only when

\[
s_\alpha=|S_\alpha|\ge2.
\]

Set

\[
T_\alpha
=
\begin{cases}
\dfrac{u_\alpha(4s_\alpha-u_\alpha-2r_\alpha)_+}{12},
& s_\alpha\ge2,\\[1.2ex]
0,
& s_\alpha\le1.
\end{cases}
\]

Then define

\[
z_{\alpha,ij}
=
\frac{T_\alpha}{\binom{s_\alpha}{2}},
\qquad ij\subseteq S_\alpha,
\]

only for debit-active groups.

### Meaning

Groups with one-vertex or zero-vertex subcores are not used for quadratic core-edge triangle savings. Their edges are either handled by internal local packings or left unused and charged to the residual ledger. This weakens the packing but avoids an invalid formula.

---

## 4. Correction C — Multi-core / retained-core bookkeeping

### Problem in v0.2

The ownership convention was present but too compressed. It could be read as if retained cores had to be disjoint, or as if multi-core overlaps were hidden in lower-order terms.

### v0.3 correction

Paper C now contains a standalone lemma:

> **Retained-core ownership ledger.** Run the nearest-heavy recursion with the retained-core convention. Then every edge has a single active owner: internal, boundary, core, or unused. If an edge lies in multiple retained cores, it is owned by the deepest retained core containing both endpoints. Retained-core edges are excluded from descendant relative edge sets.

### Key proof point

The clique-tree recursion is laminar. If a vertex support meets two child components after splitting at a bag `b`, then by connectedness the support contains `b`. Therefore that vertex is retained as boundary/core, not private in both children. This gives disjoint private sets and prevents duplicate internal ownership.

Edges inside overlapping retained cores are assigned to the deepest retained core containing both endpoints. Descendants cannot reuse those edges because retained-core edges are removed from relative edge sets.

### Result

Nested or overlapping retained cores are allowed. What is single-valued is not vertex membership, but **edge-capacity ownership**.

---

## 5. What remains conditional after v0.3

v0.3 makes the global fractional assembly more defensible, but it does not by itself attach all local finite proof data.

The remaining referee-sensitive items are:

1. **Promotion completeness / terminal classification.**  
   Paper B must give exact thresholds separating bounded local residues from long-core or overload promotion events.

2. **`L_4` certificate package.**  
   The public repository should include the rational certificate, exact verifier, type list, edge atoms, triangle atoms, rational weights, and ownership mode.

3. **Core-Fan/Farkas normalization.**  
   Paper B must spell out the capacity normalization, compressed-fan reduction, and Hall/Farkas dual argument.

4. **Integral rounding.**  
   Paper D should explicitly cite Haxell--Rodl / Yuster for
   \[
   \nu_3(G)\ge \nu_3^*(G)-o(n^2)
   \]
   for the fixed family `{K_3}`.

---

## 6. Suggested response to reviewer

> Thank you — this is a fair reading of v0.2. The multi-core bookkeeping was not intended to be hidden inside lower-order terms. The intended mechanism is the retained-core ownership ledger: every edge is assigned to a unique active account — internal, boundary, retained-core, or unused — and retained-core edges are explicitly removed from descendant relative accounts. In v0.3 we promote this convention to a standalone lemma in Paper C.
>
> We also agree with the two Codex comments. The weighted Heavy-Bag statement must use the weighted bag maximum `M_x^*`, not the unweighted `M_*`. The uniform boundary-debit formula must be restricted to debit-active groups with `s_alpha >= 2`; groups with `s_alpha <= 1` have no core edge on which a triangle `uij` can realize the debit, so they are assigned to the residual ledger.
>
> The remaining local items are promotion completeness, the reproducible `L_4` certificate package, and the final Core-Fan/Farkas normalization proof. The global fractional assembly in Paper C is now stated conditionally on those Paper B inputs.

---

## 7. Commit suggestions

```text
Fix weighted Heavy-Bag lemma using weighted bag maximum
```

```text
Restrict uniform boundary-debit realization to debit-active subcores
```

```text
Add retained-core ownership ledger for recursive multi-core bookkeeping
```

```text
Record v0.3 proof-status audit and reviewer corrections
```
