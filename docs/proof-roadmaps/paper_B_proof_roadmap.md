# Proof Roadmap — Paper B

## Paper B purpose

Paper B proves the local chordal toolkit needed by Paper C.

Its core output is:

\[
\boxed{
\text{every terminal local chordal region is discharged, promoted, or certified.}
}
\]

Paper B should be readable without inspecting the historical gates.

## Inputs imported

Paper B may import from Paper A:

1. chordal graph and clique-tree conventions;
2. connected subtree / Helly facts;
3. nearest-heavy laminar decomposition framework;
4. definitions of regions, branches, corridors, retained cores, and terminal regions;
5. diffuse-region setup.

Paper B may also use standard external facts about chordal graphs, perfect elimination orderings, Farkas/flow duality, and finite exact certificate verification.

## Outputs exported to Paper C

Paper B exports:

1. Weighted Heavy-Bag Lemma;
2. Core-Fan/Farkas allocation theorem;
3. debit-active boundary group convention;
4. single-ear budget lemma;
5. bounded-multiplicity simplicial sweep;
6. overload extraction lemma;
7. Boundary-Export \(L_4\) local certificate statement;
8. Terminal No-Escape Classification.

## Main proof chain

### Step 1. Weighted Heavy-Bag Lemma

For nonnegative weights \(x_v\), define

\[
M_x^*=\max_t\sum_{v:t\in\mathcal T_v}x_v.
\]

Then:

\[
\sum_{uv\in E(G)}x_ux_v
\le
M_x^*\sum_vx_v.
\]

The unweighted case follows by taking \(x_v=1\).

This corrects the false form using an unweighted bag maximum for arbitrary weights.

---

### Step 2. Debit-active boundary groups

Boundary groups with retained subcore size

\[
s_\alpha\le1
\]

are not debit-active. They contain no core edge on which a local triangle \(uij\) can realize a quadratic boundary debit.

Only groups with

\[
s_\alpha\ge2
\]

enter the quadratic core-capacity ledger.

---

### Step 3. Core-Fan/Farkas allocation

Given active boundary debits \(T_\alpha\) supported on subcores \(S_\alpha\), Paper B proves Hall-type capacity inequalities:

\[
\sum_{\alpha\in\mathcal A}T_\alpha
\le
\operatorname{Cap}\left(\bigcup_{\alpha\in\mathcal A}E(S_\alpha)\right)
\]

for every active subfamily \(\mathcal A\).

By Farkas/flow duality, this gives an allocation of all active debits into retained-core edge capacity.

This is exported to Paper C.

---

### Step 4. Single-ear budget

A simplicial ear of mass \(a\) attached to a clique separator of mass \(\sigma\) requires budget

\[
B(a,\sigma)=\frac12 a(\sigma-a)_+.
\]

Since

\[
B(a,\sigma)\le\frac{\sigma^2}{8},
\]

one ear consumes at most one quarter of the separator's internal capacity scale.

---

### Step 5. Bounded-multiplicity simplicial sweep

For each separator edge/loop atom \(e\), define its sweep multiplicity

\[
m(e)=|\{i:e\subseteq S_i\}|.
\]

If

\[
m(e)\le4
\]

for every atom \(e\), then the proportional budget assignment loads each atom by at most its capacity.

Thus bounded multiplicity is absorbed locally.

---

### Step 6. Overload extraction

If some separator atom has

\[
m(e)\ge5,
\]

the local ear-by-ear budget scale is no longer correct.

By the chordal connected-subtree / Helly structure, the ears requesting \(e\) share a common core locus.

Then one of the following occurs:

1. bounded common-core/sunflower promotion;
2. drifting long-core/five-window promotion;
3. lower-order residue if the mass is below threshold.

Thus multiplicity-five overload is not a new terminal obstruction.

---

### Step 7. Boundary-Export \(L_4\)

After good-tail reduction, ear-budget absorption, and overload extraction, the remaining bounded span-four residue is handled by Boundary-Export \(L_4\).

Boundary types are counted by rank:

\[
\rho(B)=|B|.
\]

If

\[
\rho(B)\le2,
\]

the finite boundary-export certificate applies.

Triangle usage is classified by the number \(b\) of boundary vertices:

\[
b=0:\text{ internal local triangle;}
\]

\[
b=1:\text{ mixed local triangle;}
\]

\[
b=2:\text{ exported core debit;}
\]

\[
b=3:\text{ pure parent-core triangle, forbidden locally.}
\]

If

\[
\rho(B)\ge3,
\]

the object is no longer a local \(L_4\) problem. It is parent-core involvement and is promoted or globally allocated.

---

### Step 8. Terminal No-Escape Classification

Every bounded span-four terminal residue falls into one of:

1. diffuse discharge;
2. good-tail/good-leaf reduction;
3. bounded-multiplicity ear absorption;
4. overload promotion;
5. Boundary-Export \(L_4\);
6. parent-core/global allocation;
7. lower-order residue.

Therefore there is no fourth triangular span-four terminal obstruction.

## Reviewer-sensitive wording

Paper B should say:

\[
\boxed{
L_4\text{ is not used as an unrestricted window-sweep theorem.}
}
\]

It is used only after structural reduction and boundary-rank control.

## What Paper B does not prove

Paper B does not prove the global fractional theorem. That is Paper C.

Paper B does not prove the integral clique-partition theorem. That is Paper D.

Paper B does not rely on Paper C or Paper D.
