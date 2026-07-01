# Reviewer-Sensitive Points

This file lists points likely to attract reviewer attention and how the preprint series handles them.

## 1. Weighted Heavy-Bag Lemma

### Risk

Using the unweighted bag maximum \(M_*\) for arbitrary vertex weights is false.

### Fix

Use:

\[
M_x^*
=
\max_t\sum_{v:t\in\mathcal T_v}x_v.
\]

Then:

\[
\sum_{uv\in E(G)}x_ux_v
\le
M_x^*\sum_vx_v.
\]

## 2. Boundary groups with \(s_\alpha\le1\)

### Risk

The formula

\[
z_{\alpha,ij}=
\frac{T_\alpha}{\binom{s_\alpha}{2}}
\]

is undefined for \(s_\alpha=0,1\).

### Fix

Only groups with:

\[
s_\alpha\ge2
\]

are debit-active. Groups with \(s_\alpha\le1\) have no quadratic core-edge debit.

## 3. Ownership ledger versus quantitative bound

### Risk

The ownership ledger proves feasibility, not the \(n^2/6\) bound.

### Fix

Separate:

\[
\text{ownership ledger}
\Rightarrow
\text{no double-loading of edges};
\]

from:

\[
\text{local amortized inequalities}
+
\text{telescoping}
\Rightarrow
\frac{n^2}{6}+o(n^2).
\]

## 4. Multi-core overlap

### Risk

Nested retained cores may overlap in vertices or subcore traces.

### Fix

Ownership is edge-wise.

A load on core edge \(ij\) is charged to the owner of \(ij\), not to an assumed owner of the whole subcore \(S_\alpha\).

## 5. \(L_4\) is not universal window-sweep

### Risk

A reviewer may object that arbitrary interacting span-four windows cannot be swept by \(L_4\).

### Fix

The preprint does not claim an unrestricted window-sweep theorem.

It uses:

\[
\text{Budgeted Simplicial Sweep}
+
\text{Overload Promotion}
+
\text{Boundary-Export }L_4.
\]

## 6. Multiplicity threshold

### Risk

The step from local overload to promotion may look narrative.

### Fix

State the overload extraction explicitly:

\[
m(e)\le4
\Rightarrow
\text{local budget passes}.
\]

\[
m(e)\ge5
\Rightarrow
\text{common-core/sunflower, long-core/five-window, or lower-order residue}.
\]

## 7. Boundary rank three

### Risk

Boundary rank three can fail if pure-boundary triangles are forbidden.

### Fix

Boundary rank three is not certified locally.

\[
\rho(B)\ge3
\Rightarrow
\text{parent-core involvement}.
\]

It is promoted or globally allocated.

## 8. Role of the computational certificate

### Risk

The proof may look dependent on a black-box LP.

### Fix

The structural proof reduces the remaining \(L_4\) component to finitely many rank-\(\le2\) boundary-export cases.

The certificate is exact, finite, and reproducible. It validates only the final local residue.

## 9. Paper C dependency on Paper B

### Risk

Paper C may appear to reprove or assume local toolkit details.

### Fix

Paper C imports Paper B outputs explicitly and only assembles them through ownership and telescoping.

## 10. Paper D rounding

### Risk

Integral rounding may appear to feed back into the fractional proof.

### Fix

Paper D is downstream only.

It uses:

\[
\nu_3(G)\ge\nu_3^*(G)-o(n^2)
\]

and does not influence Paper B or Paper C.
