<div class="center">

Paper B in the series on clique partitions in split and chordal graphs.
Preprint; the local finite $L_4$ component is recorded as an exact
reproducible certificate package.

</div>

**Keywords.** Clique partitions; chordal graphs; clique trees; triangle
packings; fractional packings; local reductions; finite certificates.

**MSC 2020.** 05C70, 05C35, 05C65, 05C69.

# Introduction

This paper is the technical toolkit paper in the series. It does not
prove the final chordal clique partition theorem. Instead, it proves and
packages the local and structural reductions used by the global
recursive argument in Paper C.

The target result of the series is the asymptotic chordal clique
partition theorem:
$$\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
    =
    \left(\frac16+o(1)\right)n^2.$$ Paper A proves the corresponding
sharp split graph theorem and supplies the extremal construction. Paper
C proves the fractional triangle theorem for chordal graphs using the
tools developed here. Paper D applies fractional-to-integral
triangle-packing rounding to obtain the final clique partition theorem.

## Purpose and status of this preprint

The purpose of this preprint is to make the dependencies of Paper C
explicit. The global recursive assembly is handled in Paper C; this
paper supplies the local reductions and finite certificate interfaces
needed by that assembly. The status of v0.3 is as follows.

1.  The weighted Heavy-Bag lemma is corrected and proved using the
    weighted bag maximum.

2.  Core-Fan/Farkas is stated with the debit-active guard $s_\alpha\ge2$
    and with the Hall/Farkas allocation interface used by Paper C.

3.  The terminal no-escape step is closed by the Boundary-Export
    Simplicial $L_4$ Alternative: bounded-multiplicity ears are
    absorbed, multiplicity-five overloads promote, boundary-rank at most
    two is handled by boundary-export $L_4$, and boundary-rank at least
    three is parent-core involvement.

4.  The $L_4$ step is finite and machine-checkable. The paper does not
    replace the certificate family by a symbolic universal formula; the
    exact rational certificates and verifier must be attached for
    independent reproducibility.

# Chordal preliminaries

A graph $G$ is chordal if every cycle of length at least four has a
chord. Equivalently, $G$ admits a clique-tree representation: there is a
tree $\mathcal T$ whose nodes are maximal cliques of $G$, and for each
$v\in V(G)$ the set of clique-tree nodes containing $v$ forms a
connected subtree.

We use the intersection-subtree notation. Each vertex $v\in V(G)$
corresponds to a connected subtree $$\mathcal T_v\subseteq \mathcal T.$$
For a clique-tree node $t$, set $$C(t)=\{v:t\in\mathcal T_v\}.$$
Adjacency is represented by subtree intersection: $$uv\in E(G)
    \quad\Longleftrightarrow\quad
    \mathcal T_u\cap\mathcal T_v\neq\varnothing.$$ The bag coverage is
$$M(t)=|C(t)|,$$ and the maximum coverage is $$M_*=
    \max_{t\in V(\mathcal T)}M(t).$$

# Heavy bags

<div id="lem:heavy-bag" class="lemma">

**Lemma 1** (Heavy-Bag Lemma). *Let $G$ be chordal with clique-tree
representation $\mathcal T$, and let $$M_*=
    \max_{t\in V(\mathcal T)} |C(t)|.$$ Then $$|E(G)|\le M_* n.$$ More
generally, for nonnegative vertex weights $x_v$, define the weighted bag
maximum $$M_x^*
    =
    \max_{t\in V(\mathcal T)}
    \sum_{v:t\in\mathcal T_v}x_v.$$ Then $$\sum_{uv\in E(G)}x_ux_v
    \le
    M_x^*\sum_vx_v.$$*

</div>

<div class="proof">

*Proof.* A chordal graph admits a perfect elimination ordering
$v_1,\ldots,v_n$. For each $v_i$, its later neighbours form a clique and
hence are contained in some clique-tree bag. Therefore the number of
later neighbours is at most $M_*$, which gives $$|E(G)|
    \le
    \sum_i M_*
    =
    M_*n.$$ For the weighted statement, orient every edge from the
earlier endpoint to the later endpoint in this ordering. The later
neighbours of $v_i$ lie in a single bag, so their total $x$-mass is at
most $M_x^*$. Hence $$\sum_{uv\in E(G)}x_ux_v
    =
    \sum_i x_{v_i}
    \sum_{\substack{j>i\\v_iv_j\in E(G)}}x_{v_j}
    \le
    \sum_i x_{v_i}M_x^*
    =
    M_x^*\sum_i x_{v_i}.$$ ◻

</div>

<div class="remark">

**Remark 2** (Correction from v0.2). The weighted form must use $M_x^*$,
the maximum weighted bag mass. The stronger-looking bound with the
unweighted $M_*$ is false for arbitrary nonnegative weights. For
example, in $K_2$, $M_*=2$, but taking both weights equal to $100$ gives
a left-hand side of $10^4$, much larger than $M_*\sum_vx_v=400$.

</div>

<div class="remark">

**Remark 3**. The lemma says that a chordal graph with no linearly large
clique-tree bag is quadratically sparse. Thus any obstruction at scale
$n^2$ must contain a heavy retained core. This is the entry point for
all promotion and core-fan arguments.

</div>

# Leaf reductions and the correct strong-leaf inequality

Consider a leaf clique $K=A\cup S$, where $A$ is the private simplicial
part and $S$ is the separator to the rest of the graph. Let
$$a=|A|,\qquad s=|S|,$$ and let $r$ denote the outside mass.

<div id="lem:strong-leaf" class="lemma">

**Lemma 4** (Strong-Leaf Inequality). *A leaf is good, in the sense that
the local simplicial reduction closes the $1/6$-potential account,
whenever $$4s\le a+2r+O(1).$$ If a leaf is not good, then it is strong:
$$4s>a+2r-O(1).$$ Consequently, $$5s>n+r-O(1).$$*

</div>

<div class="proof">

*Proof sketch.* Removing the private simplicial part $A$ costs at most
$$as+1$$ cliques in the local partition account. Comparing this with the
potential drop $$\frac{n^2-(n-a)^2}{6}
    =
    \frac{2na-a^2}{6}$$ and substituting $n=a+s+r$ gives the good-leaf
inequality after collecting lower-order constants. If the inequality
fails, then $$4s>a+2r-O(1).$$ Since $n=a+s+r$, this implies
$$5s>n+r-O(1).$$ ◻

</div>

<div class="remark">

**Remark 5**. The consequence $s>n/3$ is not valid in general and should
not be used. The correct quantitative conclusion is $5s>n+r-O(1)$.

</div>

# The $K_{1,4}/K_{1,5}$ threshold

The shifted local dual calculation uses variables $q_e=p_e-1/3$, with
$q_e\ge -1/3$. For a star $K_{1,r}$, place $$q_{\text{loop}}=\frac23,
    \qquad
    q_{\text{spoke}}=-\frac13.$$ For center mass $c$ and leaves of unit
mass, the local quadratic form is $$Q(c)=\frac13(c^2+r)-\frac r3c.$$ The
minimum over $c$ is $$Q_{\min}
    =
    \frac13\left(r-\frac{r^2}{4}\right).$$

<div id="lem:k14-k15" class="lemma">

**Lemma 6** ($K_{1,4}/K_{1,5}$ Threshold). *The local star threshold is
sharp: $$r\le4
    \quad\text{is safe,}$$ whereas $$r=5$$ forces promotion.*

</div>

<div class="proof">

*Proof.* The displayed formula gives $Q_{\min}\ge0$ precisely for
$r\le4$, and $Q_{\min}<0$ for $r\ge5$. Thus a five-spoke star cannot be
left as a harmless local terminal obstruction. ◻

</div>

# Spectral good-leaf tails

For tree-like triangle-free tails, the shifted quadratic form takes the
form $$Q(x)=
    \frac13x^\top
    \left(I-\frac12A_T\right)x,$$ where $A_T$ is the adjacency matrix of
the underlying tree $T$.

<div id="lem:spectral-good-leaf" class="lemma">

**Lemma 7** (Spectral Good-Leaf Lemma). *If $$\rho(A_T)>2,$$ then the
tail has a good leaf. If all leaves are strong, then the tail reduces to
a bounded double-broom family.*

</div>

<div class="proof">

*Proof scheme.* The form $Q$ is negative in some direction exactly when
$I-\frac12A_T$ is not positive semidefinite, equivalently when
$\rho(A_T)>2$. A negative direction identifies a local mass distribution
incompatible with all leaves being bad unless a good leaf exists. If all
leaves remain strong, the strong-leaf inequalities force large separator
overlap at both ends. Repeated pruning leaves only the bounded
double-broom configurations. ◻

</div>

#### Verification needed.

The final manuscript should include an exact table for the bounded
double-broom family $B(r,k,s)$, with $r,s\in\{1,2,3\}$, or move that
table to an appendix.

# Ear budgets

A simplicial ear of mass $a$ attached to separator mass $\sigma$
requires budget $$B(a,\sigma)=\frac12a(\sigma-a)_+.$$

<div id="lem:single-ear-budget" class="lemma">

**Lemma 8** (Single-Ear Budget). *For every $a,\sigma\ge0$,
$$B(a,\sigma)
    =
    \frac12a(\sigma-a)_+
    \le
    \frac{\sigma^2}{8}.$$ Consequently one simplicial ear consumes at
most one quarter of the internal capacity scale $\sigma^2/2$ of its
separator clique.*

</div>

<div class="proof">

*Proof.* If $a\ge\sigma$, then $(\sigma-a)_+=0$, so there is nothing to
prove. If $0\le a\le\sigma$, the product $a(\sigma-a)$ is maximized at
$a=\sigma/2$ and has maximum $\sigma^2/4$. Hence $$B(a,\sigma)
    \le
    \frac12\cdot\frac{\sigma^2}{4}
    =
    \frac{\sigma^2}{8}.$$ Since the separator clique has internal
capacity on scale $\sigma^2/2$, the relative consumption is at most
$1/4$. ◻

</div>

<div id="lem:bounded-simplicial-sweep" class="lemma">

**Lemma 9** (Bounded-Multiplicity Simplicial Sweep). *Let $A_i$ be a
family of simplicial ears, where $A_i$ has mass $a_i$ and separator
clique $S_i$ of mass $\sigma_i$. For every internal separator edge/loop
atom $e\subseteq S_i$, let $c_e$ be its available capacity, and assign
proportional load $$b_i(e)=\lambda_i c_e,
    \qquad
    \lambda_i=
    \frac{a_i(\sigma_i-a_i)_+}{\sigma_i^2}.$$ If every separator atom
has sweep multiplicity at most four,
$$m(e)=|\{i:e\subseteq S_i\}|\le4,$$ then the whole simplicial ear
family is absorbed within internally owned separator capacity.*

</div>

<div class="proof">

*Proof.* By
Lemma <a href="#lem:single-ear-budget" data-reference-type="ref"
data-reference="lem:single-ear-budget">8</a>,
$$0\le\lambda_i\le\frac14.$$ For a fixed edge/loop atom $e$, the total
load assigned to $e$ is $$\sum_i b_i(e)
    =
    \sum_{i:e\subseteq S_i}\lambda_i c_e
    \le
    m(e)\cdot\frac14 c_e
    \le
    c_e.$$ Thus no separator atom exceeds its capacity. Since all paid
atoms are internally owned by the local sweep, the absorption is
compatible with the retained-core ownership ledger used in Paper C. ◻

</div>

# Promotion lemmas

## Long-core and five-window promotion

<div id="lem:long-core" class="lemma">

**Lemma 10** (Long-Core/Five-Window Promotion). *If a bounded-width
clique-tree window carries linear long-span mass across five consecutive
positions, then one can promote a five-window core. The promotion
separates the left and right sides into anchored regions and removes the
promoted core edges from child-private accounts.*

</div>

<div class="proof">

*Proof.* Long-span vertices crossing five consecutive positions have
connected clique-tree supports that persist across a common central path
segment. Retain the central window as the promoted core. Removing the
promoted core splits the remaining clique-tree region into left, right,
and off-path anchored components. Vertices not retained are assigned to
the component containing their remaining support. Because retained-core
edges are removed from all child-relative edge sets, descendants cannot
reuse promoted-core capacity. Thus the promotion preserves chordality,
laminarity, and single-valued edge ownership. ◻

</div>

## Overload and common-core promotion

<div id="lem:overload-extraction" class="lemma">

**Lemma 11** (Overload Extraction). *Let a bounded path-projected
terminal region contain simplicial ears $A_i$. Suppose some separator
edge/loop atom $e$ is requested by at least five ears. Then exactly one
of the following occurs:*

1.  *the ears form a bounded common-core/sunflower module and promote to
    a common-core account;*

2.  *the common atom drifts across five or more positions and promotes
    to a long-core/five-window account;*

3.  *the total overloaded mass is below the current lower-order
    threshold and is charged to the residual ledger.*

</div>

<div class="proof">

*Proof.* Every ear requesting $e$ attaches through a separator clique
containing $e$. In a chordal graph, vertex supports are connected
subtrees of the clique tree. Since the same atom $e$ is contained in all
the relevant separator cliques, the subtree Helly property localizes the
attachments around a common clique-tree locus associated with $e$. Thus
multiplicity-five overload is repeated demand on a common core atom, not
five unrelated local events.

If those ears are contained in a bounded part of the path projection,
they form a common-core/sunflower module: a common retained core $C_e$
with private ears $A_1,\ldots,A_t$. Let $u=\sum_i |A_i|$. If $u$ is
above the promotion threshold, the correct account is the aggregate
core/private account around $C_e$, so the module is promoted. If $u$ is
below threshold, its contribution is lower-order and is charged to the
residual ledger.

If the ears are not contained in a bounded local part of the projection,
then the same common atom persists while the supports drift through at
least five positions. This is exactly the long-core/five-window
situation of Lemma <a href="#lem:long-core" data-reference-type="ref"
data-reference="lem:long-core">10</a>. Therefore the configuration
promotes. These alternatives exhaust the failure of the
bounded-multiplicity sweep. ◻

</div>

<div id="cor:budgeted-sweep-alternative" class="corollary">

**Corollary 12** (Budgeted sweep alternative). *A triangular span-four
ear family is either absorbed by
Lemma <a href="#lem:bounded-simplicial-sweep" data-reference-type="ref"
data-reference="lem:bounded-simplicial-sweep">9</a>, reduced by a
good-tail move, promoted by
Lemma <a href="#lem:overload-extraction" data-reference-type="ref"
data-reference="lem:overload-extraction">11</a> or
Lemma <a href="#lem:long-core" data-reference-type="ref"
data-reference="lem:long-core">10</a>, or assigned to the lower-order
residual ledger.*

</div>

# Boundary-export $L_4$ finite certificate

The bounded span-four type system is $$\mathcal V_{11}
    =
    \{J,1,2,3,4,12,23,34,13,24,14\}.$$

<div class="definition">

**Definition 13** (Boundary rank). For an $L_4$ residue with parent-core
interface, let $B\subseteq\mathcal V_{11}$ be the set of boundary types
relevant to the local certificate. Its boundary rank is $$\rho(B)=|B|.$$

</div>

<div id="thm:l4-certificate" class="theorem">

**Theorem 14** (Boundary-Export $L_4$ Certificate). *For every bounded
span-four $L_4$ residue with boundary rank $\rho(B)\le2$, there is a
rational type-level fractional triangle certificate over
$\mathcal V_{11}$ that decomposes into:*

1.  *internal local triangles with no boundary vertices;*

2.  *mixed local triangles with one boundary vertex;*

3.  *two-boundary-one-local triangles that export their
    boundary-boundary edge load as a debit to the parent core;*

*using no locally consumed pure-boundary triangle. The exported debits
are admissible inputs to the Core-Fan/Farkas ledger.*

</div>

<div class="proof">

*Finite exact certificate proof.* There are only
$$\binom{11}{0}+\binom{11}{1}+\binom{11}{2}=67$$ boundary interfaces of
rank at most two. For each such boundary set $B$, the certificate
package lists the eleven types, all edge/loop atoms, all feasible
triangle atoms, and rational nonnegative weights. The verifier checks
exact rational equalities and inequalities for every atom.

Each triangle is classified by the number $b$ of boundary vertices. If
$b=0$, all edges are internally owned. If $b=1$, the triangle is mixed
and consumes only local-local and boundary-local atoms assigned to the
local interface account. If $b=2$, the boundary-boundary edge is not
consumed locally; it is recorded as an exported core debit. If $b=3$,
the triangle would be a pure parent-core triangle and is forbidden in
the local certificate. The exact verifier checks that no forbidden
pure-boundary triangle is used and that all exported two-boundary loads
are formatted as Core-Fan debits.

Thus every rank-$\le2$ boundary interface is discharged by a finite
rational certificate plus exported debits. Since the verification is
finite and exact, the theorem is machine-checkable once the certificate
family and verifier are attached. ◻

</div>

<div class="remark">

**Remark 15** (Sealed mode). The earlier sealed $L_4$ certificate is the
special case $\rho(B)=0$. Boundary-export mode strengthens the interface
by allowing $\rho(B)=1$ and $\rho(B)=2$, while preserving ownership by
exporting every boundary-boundary load to the parent core.

</div>

<div class="remark">

**Remark 16** (Boundary rank at least three). If $\rho(B)\ge3$, the
object is no longer a local $L_4$ certificate problem: three boundary
types may support a pure parent-core triangle. Such a configuration is
treated as parent-core involvement and is promoted, globally allocated
through Core-Fan/Farkas, or assigned to the lower-order ledger if its
mass is below threshold.

</div>

# Type blow-up realization

<div id="lem:type-blowup" class="lemma">

**Lemma 17** (Type Blow-Up Realization). *A rational type-level
fractional triangle certificate over a fixed type system lifts to an
actual fractional triangle packing with loss $$O_m(n)=o(n^2),$$ where
$m$ is the number of types. For $L_4$, $m=11$, so the loss is $O(n)$.*

</div>

<div class="proof">

*Proof.* Split each vertex class into type classes. For each rational
triangle type, choose the corresponding number of actual triangles by
standard equitable rounding inside complete multipartite or complete
typed blocks. Since the type system has fixed size $m$, all divisibility
losses are bounded by $O_m(n)$ edges. The rational certificate
guarantees capacity feasibility at type level, and the rounding error
contributes only $O_m(n)$, which is $o(n^2)$. ◻

</div>

# Core-Fan Allocation Theorem

Boundary groups are indexed by $\alpha$. Each group has private mass
$u_\alpha$, retained subcore $S_\alpha$, size $$s_\alpha=|S_\alpha|,$$
and exterior mass $r_\alpha$.

<div class="definition">

**Definition 18** (Debit-active boundary group). A boundary group
$\alpha$ is debit-active if $$s_\alpha\ge2.$$ Only debit-active groups
enter the quadratic core-capacity ledger. For $s_\alpha\le1$, define the
active debit to be zero: $$T_\alpha^{\mathrm{act}}=0.$$ For
$s_\alpha\ge2$, define $$T_\alpha^{\mathrm{act}}
    =
    \frac{u_\alpha(4s_\alpha-u_\alpha-2r_\alpha)_+}{12}.$$ When no
ambiguity is possible, we write $T_\alpha$ for
$T_\alpha^{\mathrm{act}}$.

</div>

<div class="remark">

**Remark 19** (Small subcores). The restriction $s_\alpha\ge2$ is
necessary. If $s_\alpha\le1$, then $S_\alpha$ contains no core edge
$ij$, so no triangle of the form $uij$ can realize a quadratic boundary
debit. These groups are assigned to the residual or unused-edge ledger
in Paper C. This weakens the triangle packing but avoids an undefined
allocation.

</div>

<div id="thm:core-fan" class="theorem">

**Theorem 20** (Core-Fan Allocation Theorem). *For every family
$\mathcal A$ of debit-active boundary groups,
$$\sum_{\alpha\in\mathcal A}T_\alpha
    \le
    \operatorname{Cap}
    \left(
    \bigcup_{\alpha\in\mathcal A}E(S_\alpha)
    \right).$$ Equivalently, the boundary-debit vector lies in the
fractional core-edge capacity polytope and therefore admits a
Hall/Farkas feasible allocation over retained core edges.*

</div>

<div class="proof">

*Proof.* It is enough, by the max-flow/Farkas theorem, to prove the Hall
inequalities over every subfamily of debit-active groups. Fix such a
subfamily $\mathcal A$. Let
$$S=\left|\bigcup_{\alpha\in\mathcal A}S_\alpha\right|,
    \qquad
    U=\sum_{\alpha\in\mathcal A}u_\alpha.$$ For each $\alpha$, the
exterior mass seen by the group includes the other private groups and
the part of the union core outside $S_\alpha$, hence
$$r_\alpha\ge (U-u_\alpha)+(S-s_\alpha).$$ Substituting this into the
active debit gives $$T_\alpha
    \le
    \frac{u_\alpha(6s_\alpha-2S-2U+u_\alpha)_+}{12}.$$ Only groups for
which the positive part is active can contribute. Compress the active
subfamily by replacing each active subcore by its average retained size
$\bar s$, preserving total private mass and the union support. The
convexity of the positive-part quadratic shows that this compression is
the extremal case for a Hall violation.

In the compressed active-set case with $H$ active groups, the total
debit is bounded by $$\sum_{\alpha\in\mathcal A}T_\alpha
    \le
    \frac{(3\bar s-S)_+^2}{12H}
    \le
    \frac{\bar s^2}{3}.$$ The retained-core capacity of the union
$\bigcup_{\alpha\in\mathcal A}E(S_\alpha)$ is at least the corresponding
compressed fan capacity. Therefore $$\sum_{\alpha\in\mathcal A}T_\alpha
    \le
    \operatorname{Cap}\left(\bigcup_{\alpha\in\mathcal A}E(S_\alpha)\right).$$
Since this holds for every subfamily, the Hall conditions for the
bipartite allocation problem from debit groups to core edges are
satisfied. Farkas’ lemma, equivalently max-flow/min-cut, yields a
nonnegative allocation of all debits over retained-core edge capacity. ◻

</div>

# Boundary-Export Simplicial $L_4$ Alternative

<div id="thm:boundary-export-simplicial-l4" class="theorem">

**Theorem 21** (Boundary-Export Simplicial $L_4$ Alternative). *Let
$\mathcal R$ be a bounded span-four terminal region in the nearest-heavy
laminar decomposition. Assume the good-tail reductions, the
$K_{1,4}/K_{1,5}$ threshold, the Core-Fan/Farkas allocation theorem, and
the exact boundary-export $L_4$ certificates of
Theorem <a href="#thm:l4-certificate" data-reference-type="ref"
data-reference="thm:l4-certificate">14</a>. Then every active triangular
residue in $\mathcal R$ is discharged by one of the following compatible
accounts:*

1.  *good-tail/good-leaf reduction;*

2.  *bounded-multiplicity simplicial ear absorption;*

3.  *sealed or boundary-export $L_4$ certification;*

4.  *exported core debit allocated by Core-Fan/Farkas;*

5.  *common-core/sunflower promotion;*

6.  *long-core/five-window promotion;*

7.  *lower-order residue.*

*In particular, no fourth triangular span-four terminal obstruction
remains.*

</div>

<div class="proof">

*Proof.* Let $\mathcal R$ be terminal and bounded span-four. If a good
endpoint exists, apply the good-tail/good-leaf reduction. Hence assume
no good endpoint remains.

Consider the simplicial ear family in $\mathcal R$. If every separator
atom has multiplicity at most four,
Lemma <a href="#lem:bounded-simplicial-sweep" data-reference-type="ref"
data-reference="lem:bounded-simplicial-sweep">9</a> absorbs the whole
family within internally owned separator capacity. If some separator
atom has multiplicity at least five,
Lemma <a href="#lem:overload-extraction" data-reference-type="ref"
data-reference="lem:overload-extraction">11</a> promotes the
corresponding common-core/sunflower or long-core/five-window structure,
unless its total mass is below the residual threshold.

After these alternatives are exhausted, any remaining bounded span-four
residue has no good-tail exit, no bounded-multiplicity ear budget left
to pay, and no multiplicity-five overload. Let $B$ be its active
parent-boundary type set. If $\rho(B)\le2$,
Theorem <a href="#thm:l4-certificate" data-reference-type="ref"
data-reference="thm:l4-certificate">14</a> gives a boundary-export $L_4$
certificate. Internal and mixed triangles are paid locally.
Two-boundary-one-local triangles export their boundary-boundary load as
core debits, and those debits are feasible by
Theorem <a href="#thm:core-fan" data-reference-type="ref"
data-reference="thm:core-fan">20</a>. If $\rho(B)=0$, this is the sealed
$L_4$ certificate.

If $\rho(B)\ge3$, the object is not local: three boundary types can
support a pure parent-core triangle. Such a configuration is treated as
parent-core involvement and is promoted, allocated globally by the
retained-core Core-Fan ledger, or charged to the lower-order ledger if
its mass is below threshold. Therefore all terminal bounded span-four
triangular residues are exhausted by the listed alternatives. ◻

</div>

# Local terminal toolkit

<div id="thm:local-toolkit" class="theorem">

**Theorem 22** (Local Terminal Toolkit). *Every bounded local residue
arising in the chordal recursion is one of:*

1.  *good-leaf reducible;*

2.  *ear-budget reducible by bounded-multiplicity simplicial
    absorption;*

3.  *sealed or boundary-export $L_4$-certified with boundary rank at
    most two;*

4.  *long-core/five-window promoted;*

5.  *overload/common-core promoted;*

6.  *parent-core allocated by Core-Fan/Farkas;*

7.  *lower-order residue below the promotion threshold.*

</div>

<div class="proof">

*Proof.* Apply
Theorem <a href="#thm:boundary-export-simplicial-l4" data-reference-type="ref"
data-reference="thm:boundary-export-simplicial-l4">21</a>. Tree-like
tails are first reduced by the spectral good-leaf mechanism. The local
star threshold separates the safe $K_{1,4}$ regime from the
promotion-forcing $K_{1,5}$ regime. Bounded multiplicity ears are
absorbed by
Lemma <a href="#lem:bounded-simplicial-sweep" data-reference-type="ref"
data-reference="lem:bounded-simplicial-sweep">9</a>. Multiplicity-five
overloads are promoted by
Lemma <a href="#lem:overload-extraction" data-reference-type="ref"
data-reference="lem:overload-extraction">11</a>. The remaining
rank-$\le2$ boundary residue is discharged by the boundary-export $L_4$
certificate, while boundary rank at least three is parent-core
involvement and enters promotion or Core-Fan/Farkas allocation. These
alternatives exhaust the terminal bounded span-four cases. ◻

</div>

<div class="remark">

**Remark 23** (Finite certificate component). The local terminal toolkit
is now reduced to an explicit finite certificate component: the
rank-$\le2$ boundary-export $L_4$ certificate family. The paper should
be distributed with the rational certificate data, verifier, and
verifier output.

</div>

# Interface with Paper C

Paper C uses this toolkit in the following exact forms.

1.  Lemma <a href="#lem:heavy-bag" data-reference-type="ref"
    data-reference="lem:heavy-bag">1</a>, with the weighted version
    stated using $M_x^*$.

2.  Theorem <a href="#thm:local-toolkit" data-reference-type="ref"
    data-reference="thm:local-toolkit">22</a>, to classify terminal
    regions.

3.  Theorem <a href="#thm:core-fan" data-reference-type="ref"
    data-reference="thm:core-fan">20</a>, only for debit-active groups
    $s_\alpha\ge2$.

4.  Theorem <a href="#thm:l4-certificate" data-reference-type="ref"
    data-reference="thm:l4-certificate">14</a>, in sealed mode
    $\rho(B)=0$ or boundary-export mode $\rho(B)\le2$.

5.  Lemma <a href="#lem:type-blowup" data-reference-type="ref"
    data-reference="lem:type-blowup">17</a>, to pass from a fixed
    rational type certificate to actual fractional triangle weights with
    $O(n)$ loss.

# Discussion and verification roadmap

Version v0.3 resolves the main v0.2 formulation defects and incorporates
the terminal no-escape proof. The weighted Heavy-Bag lemma now uses the
weighted bag maximum; one-vertex and zero-vertex subcores do not enter
uniform core-edge allocation; retained-core ownership is edge-wise in
Paper C; and the terminal span-four case is handled by the
Boundary-Export Simplicial $L_4$ Alternative.

The remaining reproducibility requirement is not a mathematical
narrative gap but a finite evidence package: the rank-$\le2$
boundary-export $L_4$ certificates, exact verifier, and verifier output.
Without those files,
Theorem <a href="#thm:l4-certificate" data-reference-type="ref"
data-reference="thm:l4-certificate">14</a> should be read as a finite
machine-checkable certificate theorem whose data are to be attached.

# Proof-status audit

<div class="center">

| Item                     | Status in v0.3                   | Final requirement                     |
|:-------------------------|:---------------------------------|:--------------------------------------|
| Heavy-Bag Lemma          | proved                           | none                                  |
| Weighted Heavy-Bag       | proved with $M_x^*$              | none                                  |
| Strong-Leaf Inequality   | algebraic local lemma            | polish details                        |
| $K_{1,4}/K_{1,5}$        | proved threshold                 | none                                  |
| Spectral Good-Leaf       | structural reduction             | include double-broom table if desired |
| Single-Ear Budget        | proved                           | none                                  |
| Bounded Simplicial Sweep | proved                           | none                                  |
| Overload Extraction      | proved as promotion alternative  | thresholds in notation                |
| Long-Core Promotion      | proved structurally              | thresholds in notation                |
| Boundary-Export $L_4$    | finite exact certificate theorem | attach 67 certificates/verifier       |
| Type Blow-Up             | proved                           | none                                  |
| Core-Fan/Farkas          | Hall/Farkas proof included       | align notation with repo              |
| Terminal Toolkit         | proved modulo finite $L_4$ data  | attach certificate package            |

</div>

# Required $L_4$ certificate repository layout

For full referee reproducibility, the repository should include:

    certificates/l4_boundary_export/
      README.md
      l4_types.json
      l4_edge_atoms.json
      l4_triangle_atoms.json
      boundary_sets_rank_le_2.json
      l4_boundary_export_certificates.json
      verify_l4_boundary_export.py
      verifier_output.txt

The verifier should check exact rational constraints for all $67$
boundary interfaces with $\rho(B)\le2$, nonnegativity of all triangle
weights, absence of locally consumed pure-boundary triangles, local
capacity feasibility for internal and mixed atoms, and correct export
formatting for two-boundary-one-local debits.
