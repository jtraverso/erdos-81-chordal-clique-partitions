# Calculation Ledger — Paper B

This ledger records the calculations that Paper B uses.

## Calculation 1 — Weighted Heavy-Bag Lemma

For nonnegative vertex weights \(x_v\), define the weighted bag maximum:

\[
M_x^*
=
\max_t\sum_{v:t\in\mathcal T_v}x_v.
\]

A perfect elimination ordering orients each edge from earlier to later.

For every vertex \(v_i\), later neighbors form a clique, hence lie in some bag. Therefore their total \(x\)-mass is at most \(M_x^*\).

Thus:

\[
\sum_{uv\in E(G)}x_ux_v
=
\sum_i x_{v_i}
\sum_{\substack{j>i\\v_iv_j\in E(G)}}x_{v_j}
\le
\sum_i x_{v_i}M_x^*
=
M_x^*\sum_i x_{v_i}.
\]

Unweighted case:

\[
|E(G)|\le M_*n.
\]

## Calculation 2 — Debit-active boundary groups

If a boundary trace group has subcore size

\[
s_\alpha=|S_\alpha|\le1,
\]

then there is no core edge \(ij\subseteq S_\alpha\). Therefore no local triangle of the form \(uij\) can realize a quadratic boundary debit.

Set:

\[
T_\alpha^{\mathrm{act}}=0
\qquad
(s_\alpha\le1).
\]

For

\[
s_\alpha\ge2,
\]

use the active debit:

\[
T_\alpha
=
\frac{u_\alpha(4s_\alpha-u_\alpha-2r_\alpha)_+}{12}.
\]

## Calculation 3 — Core-Fan/Farkas Hall form

For an active subfamily \(\mathcal A\), prove:

\[
\sum_{\alpha\in\mathcal A}T_\alpha
\le
\operatorname{Cap}\left(\bigcup_{\alpha\in\mathcal A}E(S_\alpha)\right).
\]

Then Farkas/flow gives nonnegative allocations \(y_{\alpha,e}\) satisfying:

\[
\sum_{e\in E(S_\alpha)}y_{\alpha,e}=T_\alpha,
\]

and

\[
\sum_{\alpha:e\in E(S_\alpha)}y_{\alpha,e}\le c_e.
\]

This is the capacity realization needed by Paper C.

## Calculation 4 — Single-ear budget

A simplicial ear of mass \(a\) with separator mass \(\sigma\) has absorption budget:

\[
B(a,\sigma)=\frac12 a(\sigma-a)_+.
\]

The maximum occurs at \(a=\sigma/2\), hence:

\[
B(a,\sigma)\le\frac{\sigma^2}{8}.
\]

The separator clique capacity scale is:

\[
\frac{\sigma^2}{2}.
\]

Therefore one ear uses at most:

\[
\frac{\sigma^2/8}{\sigma^2/2}
=
\frac14
\]

of separator capacity.

## Calculation 5 — Proportional atom budget

For ear \(A_i\) with separator mass \(\sigma_i\), define:

\[
\lambda_i=
\frac{a_i(\sigma_i-a_i)_+}{\sigma_i^2}.
\]

Then:

\[
0\le\lambda_i\le\frac14.
\]

For separator atom \(e\subseteq S_i\) with capacity \(c_e\), assign:

\[
b_i(e)=\lambda_i c_e.
\]

## Calculation 6 — Multiplicity at most four

Let:

\[
m(e)=|\{i:e\subseteq S_i\}|.
\]

If

\[
m(e)\le4
\]

for every separator atom \(e\), then:

\[
\sum_i b_i(e)
=
\sum_{i:e\subseteq S_i}\lambda_i c_e
\le
m(e)\cdot\frac14c_e
\le
c_e.
\]

Thus bounded multiplicity is capacity-feasible.

## Calculation 7 — Multiplicity at least five

If

\[
m(e)\ge5,
\]

then the ear-by-ear local scale is no longer used.

The five-or-more ears share a common separator atom \(e\), hence a common core locus in the clique-tree.

Then:

- bounded support gives common-core/sunflower promotion;
- drifting support gives long-core/five-window promotion;
- subthreshold total mass goes to lower-order residue.

This is a structural extraction, not a local budget calculation.

## Calculation 8 — Boundary-export triangle accounting

For an \(L_4\) boundary interface \(B\), classify each triangle by:

\[
b=\#(\text{boundary vertices in the triangle}).
\]

Then:

\[
b=0
\Rightarrow
\text{internal local triangle}.
\]

\[
b=1
\Rightarrow
\text{mixed local triangle}.
\]

\[
b=2
\Rightarrow
\text{exported core debit}.
\]

\[
b=3
\Rightarrow
\text{pure parent-core triangle, forbidden locally}.
\]

Boundary rank:

\[
\rho(B)=|B|.
\]

If

\[
\rho(B)\le2,
\]

the boundary-export certificate verifies that no forbidden local \(b=3\) consumption is required.

If

\[
\rho(B)\ge3,
\]

the region is treated as parent-core involvement.

## Calculation 9 — Finite boundary-export check count

The \(L_4\) type universe has eleven types.

Boundary interfaces of rank at most two are:

\[
\binom{11}{0}+\binom{11}{1}+\binom{11}{2}
=
1+11+55
=
67.
\]

The finite certificate package should verify all 67 cases exactly.

## Calculation 10 — Terminal no-escape ledger

Every terminal bounded span-four triangular residue enters one of:

\[
\begin{array}{rcl}
\text{good endpoint} &\Rightarrow& \text{good-tail reduction},\\
m(e)\le4 &\Rightarrow& \text{budgeted ear absorption},\\
m(e)\ge5 &\Rightarrow& \text{promotion or lower-order residue},\\
\rho(B)\le2 &\Rightarrow& \text{Boundary-Export }L_4,\\
\rho(B)\ge3 &\Rightarrow& \text{parent-core involvement},\\
\text{no boundary} &\Rightarrow& \text{sealed }L_4.
\end{array}
\]

Thus no additional triangular span-four obstruction remains.
