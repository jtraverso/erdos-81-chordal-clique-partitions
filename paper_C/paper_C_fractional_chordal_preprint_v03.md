<div class="center">

Paper C in the series on clique partitions in split and chordal graphs.
Preprint; imports the finite boundary-export $L_4$ certificate
package from Paper B.

</div>

**Keywords.** Clique partitions; chordal graphs; clique trees; triangle
packings; fractional packings; edge clique partitions; Erdős problems.

**MSC 2020.** 05C70, 05C35, 05C65, 05C69.

# Introduction

The edge clique partition number of a graph $G$, denoted
$\operatorname{cp}(G)$, is the minimum number of cliques whose edge sets
partition $E(G)$. A triangle packing immediately gives a clique
partition upper bound: starting from singleton-edge cliques, every
edge-disjoint triangle can be replaced by one triangle clique, saving
two cliques. Thus $$\operatorname{cp}(G)\le |E(G)|-2\nu_3(G).$$ For
dense asymptotic questions it is natural to pass through fractional
triangle packings. This paper proves the fractional chordal theorem
needed for the chordal clique partition problem.

## Role in the series

The papers are organized as follows.

1.  Paper A proves the sharp split graph theorem and supplies the
    lower-bound construction $K_p\vee\overline{K}_{2p}$.

2.  Paper B proves the local and structural toolkit for chordal graphs:
    heavy bags, local reductions, $L_4$ certificates, promotion lemmas,
    and the Core-Fan Allocation Theorem.

3.  Paper C, the present paper, proves the global fractional triangle
    theorem for chordal graphs using Paper B.

4.  Paper D applies fractional-to-integral triangle-packing rounding and
    derives the final chordal clique partition theorem.

This paper does not prove the split lower bound and does not perform the
final integral rounding.

## Main theorem

<div id="thm:fractional-main" class="theorem">

**Theorem 1** (Fractional Chordal Theorem). *Assuming the complete Paper
B local toolkit in the form stated in
Section <a href="#sec:imported-toolkit" data-reference-type="ref"
data-reference="sec:imported-toolkit">4</a>, every chordal graph $G$ on
$n$ vertices satisfies $$|E(G)|-2\nu_3^*(G)
    \le
    \left(\frac16+o(1)\right)n^2.$$*

</div>

At the level of this preprint, the theorem is proved as an
implication from the Paper B toolkit. The main new ingredients in this
paper are the anchored recursive decomposition, the uniform realization
of boundary debits, the retained-core ownership ledger, and the global
amortization.

# Fractional triangle packings

Let $K_3(G)$ denote the set of triangles in $G$. A fractional triangle
packing is a choice of weights $$\psi_T\ge0
    \qquad
    (T\in K_3(G))$$ such that $$\sum_{T\ni e}\psi_T\le1
    \qquad
    (e\in E(G)).$$ Define $$\nu_3^*(G)=
    \max\sum_{T\in K_3(G)}\psi_T.$$ It is convenient to define the
fractional triangle residual $$\tau_3(G)=|E(G)|-2\nu_3^*(G).$$
Theorem <a href="#thm:fractional-main" data-reference-type="ref"
data-reference="thm:fractional-main">1</a> says
$$\tau_3(G)\le \left(\frac16+o(1)\right)n^2$$ for chordal graphs.

# Chordal graphs and clique trees

We use the subtree representation of chordal graphs. Let $\mathcal T$ be
a clique tree. Each vertex $v\in V(G)$ corresponds to a connected
subtree $$\mathcal T_v\subseteq\mathcal T.$$ For a clique-tree node $t$,
set $$C(t)=\{v:t\in\mathcal T_v\}.$$ Then $$uv\in E(G)
    \quad\Longleftrightarrow\quad
    \mathcal T_u\cap\mathcal T_v\neq\varnothing.$$ The bag coverage is
$$M(t)=|C(t)|.$$

# Imported toolkit from Paper B

We import the following statements from Paper B.

<div id="lem:import-heavy" class="lemma">

**Lemma 2** (Heavy-Bag Lemma, Paper B). *Let $M_* = \max_t |C(t)|$. Then
$$|E(G)|\le M_* n.$$ More generally, for nonnegative weights $x_v$,
define $$M_x^*
    =
    \max_t\sum_{v:t\in\mathcal T_v}x_v.$$ Then $$\sum_{uv\in E(G)}x_ux_v
    \le
    M_x^*\sum_vx_v.$$*

</div>

<div id="thm:import-toolkit" class="theorem">

**Theorem 3** (Local Terminal Toolkit, Paper B). *Every bounded local
residue arising in the chordal recursion is good-leaf reducible,
ear-budget reducible by bounded-multiplicity simplicial absorption,
sealed or boundary-export $L_4$-certified with boundary rank at most
two, promoted by a long-core or overload rule, assigned to parent-core
Core-Fan/Farkas allocation, or charged to the lower-order residual
ledger.*

</div>

<div id="thm:import-core-fan" class="theorem">

**Theorem 4** (Core-Fan Allocation Theorem, Paper B). *For every family
$\mathcal A$ of debit-active boundary groups, with
$s_\alpha=|S_\alpha|\ge2$, and debits $$T_\alpha
    =
    \frac{u_\alpha(4s_\alpha-u_\alpha-2r_\alpha)_+}{12},$$ one has
$$\sum_{\alpha\in\mathcal A}T_\alpha
    \le
    \operatorname{Cap}
    \left(
    \bigcup_{\alpha\in\mathcal A}E(S_\alpha)
    \right).$$*

</div>

<div id="thm:import-l4" class="theorem">

**Theorem 5** (Boundary-Export $L_4$ Certificate Theorem, Paper B).
*Every bounded span-four $L_4$ residue with boundary rank at most two
admits a rational type-level fractional triangle certificate. Internal
and mixed triangles are locally owned. Two-boundary-one-local triangles
export their boundary-boundary load as core debits. No pure-boundary
triangle is consumed locally. The sealed certificate is the rank-zero
case.*

</div>

<div id="lem:import-blowup" class="lemma">

**Lemma 6** (Type Blow-Up Realization, Paper B). *A rational type-level
fractional triangle certificate over a fixed type system lifts to an
actual fractional triangle packing with $O(n)$ loss.*

</div>

<div class="remark">

**Remark 7** (Interface status). The present preprint uses the Paper B
local toolkit and finite boundary-export $L_4$ certificate family as
imported components. The certificate data, verifier, and verifier output
must accompany Paper B for independent reproducibility.

</div>

# Anchored regions

The recursive proof works with anchored regions in the clique tree.

<div class="definition">

**Definition 8** (One-boundary branch). A one-boundary region is a pair
$$\mathcal R=(R;S),$$ where $R\subseteq\mathcal T$ is a connected
subtree and $S$ is a retained boundary clique or subcore. Its private
set is $$P(\mathcal R)
    =
    \{v:\mathcal T_v\cap R\neq\varnothing\}\setminus S.$$ Its relative
edge set is $$E^{\mathrm{rel}}(\mathcal R)
    =
    E(G[P(\mathcal R)\cup S])\setminus E(G[S]).$$

</div>

<div class="definition">

**Definition 9** (Two-boundary corridor). A two-boundary region is
$$\mathcal R=(R;S_L,S_R),$$ with two retained boundary cores. Its
private set is $$P(\mathcal R)
    =
    \{v:\mathcal T_v\cap R\neq\varnothing\}
    \setminus(S_L\cup S_R),$$ and its relative edge set is
$$E^{\mathrm{rel}}(\mathcal R)
    =
    E(G[P(\mathcal R)\cup S_L\cup S_R])
    \setminus
    \left(E(G[S_L])\cup E(G[S_R])\right).$$

</div>

Let $$m(\mathcal R)=|P(\mathcal R)|.$$ For a clique-tree node $t$
internal to $R$, define private coverage $$M_{\mathcal R}(t)
    =
    |\{v\in P(\mathcal R):t\in\mathcal T_v\}|.$$

Fix $\eta>0$. A region is $\eta$-diffuse if $$M_{\mathcal R}^*
    :=
    \max_{t\in R^\circ}M_{\mathcal R}(t)
    \le
    \eta m(\mathcal R).$$

# Nearest-heavy laminar recursion

If $\mathcal R$ is not diffuse, choose a nearest heavy bag
$b\in R^\circ$ satisfying $$M_{\mathcal R}(b)>\eta m(\mathcal R).$$
Retain $$C_b=C(b)$$ as a new core and split the tree region $R$ along
the node $b$. Components on old boundary sides become two-boundary
corridors; off-path components become one-boundary branches attached to
$C_b$.

<div id="thm:nearest-heavy" class="theorem">

**Theorem 10** (Nearest-Heavy Laminar Decomposition). *For fixed
$\eta>0$, the nearest-heavy recursion produces a finite laminar family
of anchored terminal regions and retained cores such that:*

1.  *terminal private sets are pairwise disjoint;*

2.  *retained core edges are excluded from child-private accounts;*

3.  *diffuse terminal errors sum to $O(\eta n^2)$;*

4.  *potential releases telescope under $F(x)=x^2/6$.*

</div>

<div class="proof">

*Proof.* Removing a heavy node $b$ from the tree region $R$ separates
$R$ into connected components. A component can be adjacent to the new
core $C_b$ and to at most one old boundary side, since the path between
two old boundary sides passes through $b$. Hence every child is again a
one-boundary or two-boundary region.

The number of internal clique-tree nodes strictly decreases along every
child, because $b$ becomes retained core boundary and is no longer
internal. Thus the recursion terminates.

For disjointness, suppose a vertex $v$ were private in two different
child components. Since $\mathcal T_v$ is connected and intersects both
components of $R-b$, it must contain $b$, hence $v\in C_b$. But vertices
of $C_b$ are retained as boundary/core vertices in the children, not
private vertices. Contradiction.

The same laminarity gives global disjointness of terminal private
masses: $$\sum_{\mathcal R\in\mathcal L}m(\mathcal R)\le n.$$ Diffuse
terminal regions contribute $O(\eta m(\mathcal R)^2)$, hence in total
$$\sum_{\mathcal R\in\mathcal L}O(\eta m(\mathcal R)^2)
    \le
    O(\eta n^2).$$ Finally, because private masses separated at
different recursion nodes are disjoint and retained cores are not
deleted as child-private mass, the potential drops telescope under
$F(x)=x^2/6$. ◻

</div>

# Retained-core ownership ledger

The recursion may create retained cores that overlap as vertex sets. The
proof does not require retained cores to be disjoint as sets of
vertices. It requires that every edge capacity be owned by a unique
active account.

<div id="lem:retained-core-ledger" class="lemma">

**Lemma 11** (Retained-core ownership ledger). *Run the nearest-heavy
recursion with the retained-core convention. Then there is a
single-valued ownership map $$\omega:E(G)\to
    \{\mathrm{internal},\mathrm{boundary},\mathrm{core},\mathrm{unused}\}$$
with the following properties.*

1.  *If both endpoints of an edge are private in some recursive region,
    then the edge is owned by the deepest region in which both endpoints
    are private.*

2.  *If one endpoint is private in a region and the other lies in its
    retained boundary/core, then the edge is owned by the boundary-debit
    account of that region, unless it is already internally owned by a
    deeper region.*

3.  *If both endpoints lie in one or more retained cores, then the edge
    is owned by the deepest retained core containing both endpoints.*

4.  *Retained-core edges are excluded from all descendant relative edge
    sets.*

5.  *Every boundary debit supported on a subcore $S_\alpha$ is charged
    only to the retained core owning the edges of $E(S_\alpha)$.*

6.  *No edge is used by two different local or boundary triangle-packing
    accounts.*

</div>

<div class="proof">

*Proof.* The recursion is laminar on clique-tree regions. At each
non-diffuse step, a heavy bag $b$ is retained as a core and the
remaining components of the clique-tree region become child regions.
These child regions are pairwise disjoint as tree regions, except for
their retained boundary/core vertices.

Suppose a vertex $v$ were private in two different child regions after
splitting at $b$. Since the clique-tree support $\mathcal T_v$ is
connected and meets two distinct components of $R-b$, it must contain
$b$. Hence $v\in C_b$, so $v$ is retained as a boundary/core vertex, not
private in either child. Thus child private sets are disjoint. By
induction, terminal private sets are disjoint globally.

Now fix an edge $xy\in E(G)$. Consider the set of recursive regions in
which both $x$ and $y$ are private. Since the recursion tree is laminar,
this set is linearly ordered by inclusion. If it is nonempty, choose the
deepest such region $R$. Then $xy$ is owned by the internal account of
$R$. No ancestor may also use it, and no descendant contains both
endpoints privately by maximality.

If no region contains both endpoints privately, but $x$ is private in a
region $R$ and $y\in B(R)$, then the edge $xy$ is a private-boundary
edge. It is assigned to the boundary-debit account of $R$. It cannot be
used by a child internal packing because $y$ is retained boundary/core,
not private.

Finally, if both endpoints lie in retained cores, choose the deepest
retained core containing both endpoints. That core owns $xy$. By the
retained-core convention, core edges are removed from all descendant
relative edge sets, so descendants cannot use $xy$ internally. Boundary
debits using $xy$ report edge-wise to the owner of $xy$; no assumption
is made that all edges of a boundary subcore have the same retained-core
owner.

Therefore every edge has at most one active owner. Since every local or
boundary triangle-packing source is required to use only edges owned by
its account, no edge is loaded by two different accounts. ◻

</div>

<div class="remark">

**Remark 12** (Multi-core bookkeeping). This lemma is the explicit
version of the multi-core bookkeeping used informally in earlier versions.
Nested retained cores may overlap on vertices, but edge capacity is
charged to the deepest retained core containing both endpoints.
Descendant regions never reuse retained-core edges as private capacity.

</div>

# Terminal classification

Paper B supplies the Boundary-Export Simplicial $L_4$ Alternative.

<div id="thm:terminal-classification" class="theorem">

**Theorem 13** (Terminal Classification). *Every terminal region
produced by
Theorem <a href="#thm:nearest-heavy" data-reference-type="ref"
data-reference="thm:nearest-heavy">10</a> is one of:*

1.  *an $\eta$-diffuse one-boundary branch;*

2.  *an $\eta$-diffuse two-boundary corridor;*

3.  *an atomic core-fan debit call;*

4.  *a sealed or boundary-export $L_4$-certified window with boundary
    rank at most two;*

5.  *a good-leaf or bounded-multiplicity ear-budget reducible window;*

6.  *a common-core/sunflower or long-core/five-window promotion event;*

7.  *parent-core allocation or lower-order residue.*

</div>

<div class="proof">

*Proof.* If a terminal region is diffuse, it is of type (i) or (ii).
Suppose it is not diffuse. If it had an internal heavy node, the
nearest-heavy recursion would split it further. Thus a non-diffuse
terminal region has no unresolved heavy split in the sense of the
recursion. Apply the Paper B local terminal toolkit. Good endpoints
reduce by good-leaf moves; bounded-multiplicity ears are absorbed
locally; multiplicity-five overloads promote; boundary rank at most two
is discharged by boundary-export $L_4$ with exported core debits;
boundary rank at least three is parent-core involvement and is promoted
or globally allocated. These alternatives are exactly (iii)–(vii). ◻

</div>

<div class="remark">

**Remark 14** (No unrestricted window sweep). The classification does
not use an unrestricted overlapping $L_4$ window-sweep lemma. The $L_4$
certificate is invoked only after the budgeted sweep and promotion
alternatives have reduced the residue to a sealed or boundary-export
instance of boundary rank at most two.

</div>

# Boundary debits

For a boundary trace group $\alpha$, let $u_\alpha$ be its private mass,
$S_\alpha$ its retained subcore, $s_\alpha=|S_\alpha|$, and $r_\alpha$
its exterior mass.

<div class="definition">

**Definition 15** (Active boundary debit). Define $$T_\alpha
=
\begin{cases}
\dfrac{u_\alpha(4s_\alpha-u_\alpha-2r_\alpha)_+}{12},
& s_\alpha\ge2,\\[1.2ex]
0,
& s_\alpha\le1.
\end{cases}$$ A group with $s_\alpha\ge2$ is debit-active. Groups with
$s_\alpha\le1$ do not enter the quadratic core-capacity ledger.

</div>

By the imported Core-Fan Allocation Theorem, for every family
$\mathcal A$ of debit-active groups,
$$\sum_{\alpha\in\mathcal A}T_\alpha
    \le
    \operatorname{Cap}
    \left(
    \bigcup_{\alpha\in\mathcal A}E(S_\alpha)
    \right).$$ Thus boundary debits satisfy all Hall-type capacity
inequalities over retained cores.

<div class="remark">

**Remark 16** (One-vertex and zero-vertex subcores). If $s_\alpha\le1$,
then $S_\alpha$ contains no core edge. Therefore there is no edge
$ij\subseteq S_\alpha$ on which to place a triangle $uij$. Such groups
are left unused or charged to the lower-order/diffuse residual ledger
according to the terminal classification. This only weakens the
fractional packing and prevents an undefined division by
$\binom{s_\alpha}{2}$.

</div>

# Uniform boundary-debit realization

Paper B proves that debit-active boundary debits fit in core capacity.
Paper C must realize them as actual fractional triangles.

For every debit-active group $\alpha$, define $$z_{\alpha,ij}
    =
    \frac{T_\alpha}{\binom{s_\alpha}{2}},
    \qquad
    ij\subseteq S_\alpha.$$ No such quantity is defined for
$s_\alpha\le1$.

<div id="lem:uniform-calculus" class="lemma">

**Lemma 17** (Uniform Allocation Calculus). *For $v_i\ge0$,
$V=\sum_i v_i<1$, and $0<q_i\le1-V$, $$\sum_i
\frac{
v_i(6q_i+v_i-2)_+
}{6q_i^2}
\le
\frac23.$$*

</div>

<div class="proof">

*Proof sketch.* The summand is zero unless $v_i>2-6q_i$. On each active
interval it is convex in the relevant normalized variable. Under the
constraints $v_i\ge0$, $\sum_i v_i=V$, and $q_i\le1-V$, the maximum
occurs at an extreme distribution. The one-variable extreme case reduces
to $$\frac{v(6q+v-2)}{6q^2}
    \le
    \frac23,$$ with equality only in the limiting balanced fan case.
Summing over the extremal active groups gives the displayed bound. ◻

</div>

<div id="lem:uniform-realization" class="lemma">

**Lemma 18** (Uniform Boundary-Debit Realization). *The allocation
$z_{\alpha,ij}$, restricted to debit-active groups $s_\alpha\ge2$,
realizes all active boundary debits by fractional triangles while
respecting private-boundary and core-edge capacities.*

</div>

<div class="proof">

*Proof.* For a debit-active group $\alpha$, distribute $z_{\alpha,ij}$
equally over core edges $ij\subseteq S_\alpha$. Then
$$\sum_{ij\subseteq S_\alpha}z_{\alpha,ij}=T_\alpha.$$ Each unit of
$z_{\alpha,ij}$ is realized by triangles whose private vertex lies in
group $\alpha$ and whose two core vertices are $i,j$. The
private-boundary load incident to a fixed private vertex is bounded by
the uniform fan calculation, and for a core edge $e$, the total
normalized load is bounded by
Lemma <a href="#lem:uniform-calculus" data-reference-type="ref"
data-reference="lem:uniform-calculus">17</a>. The Core-Fan Hall/Farkas
inequalities ensure that the aggregate requested core-edge load lies
within retained-core capacity.

Groups with $s_\alpha\le1$ have $T_\alpha=0$ by definition and are not
realized by core-edge triangles. Hence the allocation is well-defined
and all active debits are realized. ◻

</div>

# Boundary-export $L_4$ windows and type blow-up

Paper B supplies the Boundary-Export $L_4$ Certificate Theorem and Type
Blow-Up Realization Lemma. Thus sealed or boundary-export $L_4$ terminal
windows contribute only $O(|X|)$ local realization loss, and over
disjoint private interiors this sums to $$O_\eta(n).$$

In boundary-export mode, triangles with no boundary vertex and triangles
with one boundary vertex are locally owned. Triangles with two boundary
vertices and one local vertex export the boundary-boundary edge load as
a debit to the retained parent core; those debits enter the
Core-Fan/Farkas ledger. Pure-boundary triangles are not consumed
locally. The sealed mode is the special case of boundary rank zero.

# Edge ownership patching

<div id="thm:ownership-patching" class="theorem">

**Theorem 19** (Edge Ownership Patching Theorem). *Suppose every local,
sealed, internal, and boundary fractional triangle assignment obeys the
ownership map of
Lemma <a href="#lem:retained-core-ledger" data-reference-type="ref"
data-reference="lem:retained-core-ledger">11</a>. Then the sum of all
local assignments is a feasible global fractional triangle packing of
$G$.*

</div>

<div class="proof">

*Proof.* Let $e\in E(G)$. By
Lemma <a href="#lem:retained-core-ledger" data-reference-type="ref"
data-reference="lem:retained-core-ledger">11</a>, $e$ has at most one
active ownership account. All triangle weights produced by an account
are required to use only edges owned by that account and to respect
capacity one on those edges. Since no other account can use $e$, the
total global load on $e$ is at most one. This holds for every edge, so
the sum of all local and boundary assignments is a feasible fractional
triangle packing. ◻

</div>

# Lower-order ledger

<div id="lem:lower-order" class="lemma">

**Lemma 20** (Lower-Order Ledger). *All finite, sealed, and type-blow-up
losses are $O_\eta(n)$. Diffuse terminal losses are $O(\eta n^2)$.
Boundary groups with $s_\alpha\le1$ contribute no active quadratic debit
and are assigned to the unused or residual ledger. Therefore, after
summing over the laminar terminal family, the total unaccounted loss is
$$O(\eta n^2)+O_\eta(n).$$*

</div>

<div class="proof">

*Proof.* Terminal private sets are pairwise disjoint by
Theorem <a href="#thm:nearest-heavy" data-reference-type="ref"
data-reference="thm:nearest-heavy">10</a>. Every fixed-size certificate
or type-blow-up loss is linear in the private mass of its terminal
region, so the sum of all such losses is $O_\eta(n)$. Diffuse terminal
regions have maximum private bag coverage at most $\eta m(\mathcal R)$;
by the Heavy-Bag Lemma applied inside the private region, their
remaining internal interaction is $O(\eta m(\mathcal R)^2)$. Summing
over disjoint terminal private masses gives $O(\eta n^2)$.

Groups with $s_\alpha\le1$ do not request core-edge capacity and hence
cannot create double-counted core load. Their edges are either covered
by an internal local packing or left unused. Leaving them unused can
only increase the residual by the amount already assigned to the
terminal residual ledger. Thus they do not affect the quadratic core-fan
capacity calculation. ◻

</div>

# Proof of the fractional theorem

<div class="proof">

*Proof of
Theorem <a href="#thm:fractional-main" data-reference-type="ref"
data-reference="thm:fractional-main">1</a>.* Fix $\eta>0$. Apply the
nearest-heavy laminar recursion to the clique tree. Terminal regions are
classified by
Theorem <a href="#thm:terminal-classification" data-reference-type="ref"
data-reference="thm:terminal-classification">13</a>. Diffuse regions
contribute $O(\eta n^2)$ residual. Good-leaf and ear-budget regions are
locally reducible. Sealed or boundary-export $L_4$ windows are packed
using the imported certificate and type blow-up realization, with total
loss $O_\eta(n)$. Exported $L_4$ debits and ordinary debit-active
boundary groups report debits to their retained cores; the Core-Fan
Allocation Theorem gives capacity feasibility, and
Lemma <a href="#lem:uniform-realization" data-reference-type="ref"
data-reference="lem:uniform-realization">18</a> realizes the debits as
fractional triangles.

By Lemma <a href="#lem:retained-core-ledger" data-reference-type="ref"
data-reference="lem:retained-core-ledger">11</a> and
Theorem <a href="#thm:ownership-patching" data-reference-type="ref"
data-reference="thm:ownership-patching">19</a>, all local and boundary
triangle weights patch into one feasible global fractional triangle
packing. The potential releases telescope under $F(x)=x^2/6$, and the
lower-order ledger contributes $$O(\eta n^2)+O_\eta(n).$$ Therefore
$$|E(G)|-2\nu_3^*(G)
    \le
    \frac{n^2}{6}+O(\eta n^2)+O_\eta(n).$$ Letting $n\to\infty$ first
and then $\eta\to0$ gives $$|E(G)|-2\nu_3^*(G)
    \le
    \left(\frac16+o(1)\right)n^2.$$ ◻

</div>

# Relation to integral clique partitions

The final integral theorem is not proved in this paper. Paper D uses the
fixed-family rounding theorem of Haxell–Rödl and Yuster: $$\nu_3(G)
    \ge
    \nu_3^*(G)-o(n^2)$$ for the fixed family $\{K_3\}$. Hence
$$\operatorname{cp}(G)
    \le
    |E(G)|-2\nu_3(G)
    \le
    |E(G)|-2\nu_3^*(G)+o(n^2).$$ Combining this with
Theorem <a href="#thm:fractional-main" data-reference-type="ref"
data-reference="thm:fractional-main">1</a> yields the chordal clique
partition upper bound.

# Discussion and further directions

Theorem <a href="#thm:fractional-main" data-reference-type="ref"
data-reference="thm:fractional-main">1</a> is the conceptual center of
the series. It separates the chordal clique partition problem into two
layers: a fractional triangle-packing statement proved by clique-tree
recursion, and a final integral rounding step handled in Paper D.

Version v0.3 stabilizes three reviewer-sensitive interfaces:

1.  the weighted Heavy-Bag import now uses weighted bag maximum $M_x^*$;

2.  uniform boundary-debit realization is restricted to subcores
    $s_\alpha\ge2$;

3.  the retained-core ownership ledger is promoted to a main lemma,
    rather than hidden as lower-order bookkeeping.

The remaining reproducibility requirement is the finite Paper B
boundary-export $L_4$ certificate package. The global ownership
assembly, telescoping, and debit realization are explicit in this preprint.

# Proof-status audit

<div class="center">

| Item                              | Location          | Status in v0.3                   |
|:----------------------------------|:------------------|:---------------------------------|
| Nearest-heavy recursion           | Paper C           | proof complete             |
| Retained-core ownership ledger    | Paper C           | explicit proof added             |
| Terminal classification           | Paper C + Paper B | closed modulo finite $L_4$ data  |
| Core-Fan capacity                 | Paper B           | imported for debit-active groups |
| Uniform allocation                | Paper C           | guarded by $s_\alpha\ge2$        |
| Boundary-export $L_4$ certificate | Paper B           | imported finite exact package    |
| Type blow-up                      | Paper B           | imported                         |
| Lower-order ledger                | Paper C           | proof complete             |
| Fractional theorem                | Paper C           | conditional assembly             |
| Integral rounding                 | Paper D           | not included here                |

</div>

# Acknowledgements and use of AI-assisted tools

The author is deeply grateful to his wife María Paz and to his children
Lucas, Juan Cristóbal, Francisca, Raimundo, and Benjamín for their love,
patience, and support during the development of this work.

The author used AI-assisted tools, including Gemini 3.5 Pro and ChatGPT,
during the development of this work for exploratory search, testing
possible approaches, looking for contradictions, organizing proof
strategies, improving exposition, and preparing drafts. All mathematical
claims, proofs, citations, and final editorial decisions are the sole
responsibility of the author. No AI system is listed as an author.

<div class="thebibliography">

9

G.-T. Chen, P. Erdős, and E. T. Ordman, *Clique partitions of split
graphs*, in *Combinatorics, graph theory, algorithms and applications*
(Beijing, 1993), 21–30, 1994.

P. Erdős, E. T. Ordman, and Y. Zalcstein, *Clique partitions of chordal
graphs*, Combinatorics, Probability and Computing (1993), 409–415.

P. Erdős, A. W. Goodman, and L. Pósa, *The representation of a graph by
set intersections*, Canadian Journal of Mathematics 18 (1966), 106–112.

F. Gavril, *The intersection graphs of subtrees in trees are exactly the
chordal graphs*, Journal of Combinatorial Theory, Series B 16 (1974),
47–56.

P. E. Haxell and V. Rödl, *Integer and fractional packings in dense
graphs*, Combinatorica 21 (2001), 13–38.

R. Yuster, *Integer and fractional packing of families of graphs*,
Combinatorica 28 (2008), 245–251.

</div>
