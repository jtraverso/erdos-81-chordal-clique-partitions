# Optimal Clique Partitions under Local Perturbations

**Juan Pablo Traverso Gianini**  
Independent researcher, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Paper VI in the series — Preprint 1.0**  
**Date:** October 18, 2026  
**License:** [CC BY-NC 4.0](https://creativecommons.org/licenses/by-nc/4.0/).
Copyright © 2026 Juan Pablo Traverso Gianini.

## Abstract

We determine exact clique partition numbers in an explicit neighborhood of a complete
split graph. Write \(h=\Delta(G\triangle(K_P\vee I_O))\), where
\(|P|=p=\lfloor(n+1)/3\rfloor\), and let \(u,m,s\) count core, exterior and
crossing edges. If \(p\ge18h+1\), then \(\operatorname{cp}(G)=s-u-2m\), with an
optimum using blocks of order at most four; restricting to triangles increases the
optimum by exactly \(m\). If \(p\ge63h\), each exterior edge can be prescribed
independently to belong to a block of order four or five. For \(p\ge16\), each
prescription admits at least \(p^{\lfloor p^2/64\rfloor}\) optimal partitions.
The reference core is recoverable from degrees in the local region. We also determine
the exact additional cost caused by one exceptional vertex. That cost can be linear
even after optimizing the bipartition lower bound over every core. The constructions
attain explicit signed dual bounds by bounded-load choices and list edge coloring;
Vizing's theorem supplies the counting step. Chordality yields an exact local
stability formula but is not assumed in the principal perturbation results.


For complete joins with \(q\ge2p-1\), two legal all-\(K_5\) liftings differing on \(k\) assignments
admit optimal completions at block symmetric difference at most \(68k\).
If \(q\in\{2p-1,2p,2p+1\}\) and \(p\ge63\Delta(H)\), the all-\(K_5\)
optima with core load at most \(7\Delta(H)\) are connected by at most
\(\binom p2-2m\) steps of block distance at most \(884\).

**Keywords:** clique partition; complete split graph; local perturbation; list edge
coloring; chordal graph; exact stability.

## 1. Introduction

A clique partition of a graph is a partition of its edge set into complete subgraphs.
The blocks may share vertices and need not be maximal cliques. We write
\(\operatorname{cp}(G)\) for the minimum number of blocks and
\(\operatorname{cp}_{\le r}(G)\) when their orders are restricted to at most \(r\).

Paper IV [IV] establishes the chordal bound in Erdős 81, with the sharp integer bound for sufficiently large orders. The present paper continues the study of clique partitions beyond that global bound: it determines exact values under local perturbations, permits prescribed exterior blocks, and studies stability and restricted connectivity of optimal partitions. These results are not inputs needed to complete the proof in Paper IV.

Complete split graphs provide a useful reference family for this problem. An edge in
their complete part can support a triangle through an exterior vertex. If these triangles
are chosen compatibly, they reduce the number of single-edge blocks. Adding an exterior
edge creates further possibilities: it can be joined to a core edge to form a \(K_4\),
or to a core triangle to form a \(K_5\). The difficulty is to make all these choices
without exhausting the crossing edges needed to complete the residual core.

We show that a bound on the number of modifications at each vertex is enough to carry
out this construction and attain a classical lower bound exactly. The graph need not
be chordal. Chordality is used only afterward, when it forces the core to remain complete.

### 1.1. The local model

Let \(n\ge2\), and put
\[
p=\left\lfloor\frac{n+1}{3}\right\rfloor,\qquad
q=n-p,\qquad M(n)=\left\lfloor\frac{n(n+1)}6\right\rfloor.
\]
Fix a labeled bipartition \(V=P\sqcup O\), with \(|P|=p\) and \(|O|=q\), and let
\(S=K_P\vee I_O\). Then
\[
q\in\{2p-1,2p,2p+1\},\qquad q\ge p,\qquad
pq-\binom p2=M(n). \tag{1}
\]
For a simple graph \(G\) on this vertex set, write
\[
\begin{aligned}
C&=\binom p2-e(G[P]), &u&=e(G[P])=\binom p2-C,\\
A&=pq-e_G(P,O), &s&=e_G(P,O)=pq-A,\\
H&=G[O], &m&=e(H).
\end{aligned}
\]
Thus \(C\) and \(A\) count missing core and crossing edges, while \(m\) counts exterior
edges. The local modification parameter is
\[
h=\Delta(G\triangle S). \tag{2}
\]
All distances and types below refer to this fixed bipartition. A clique has type
\((a,b)\) if it contains \(a\) core vertices and \(b\) exterior vertices.

For \(a\in P\), let \(c_a\) and \(\alpha_a\) count its missing neighbors within the
core and in the exterior. For \(x\in O\), let \(\beta_x\) count its missing core
neighbors. The definition of \(h\) gives
\[
c_a+\alpha_a\le h,\qquad \beta_x+d_H(x)\le h,
\qquad m\le qh/2. \tag{3}
\]
The joint bounds in (3) are used in the selection steps.

### 1.2. Main results

**Theorem A (exact local formula).** If
\[
p\ge18h+1, \tag{4}
\]
then
\[
\operatorname{cp}(G)=\operatorname{cp}_{\le4}(G)
=s-u-2m=M(n)+C-A-2m. \tag{5}
\]
There is an optimal partition with \(m\) blocks \(K_4\) of type \((2,2)\),
\(u-m\) triangles of type \((2,1)\), and \(s-2u-2m\) crossing single-edge blocks.
When \(q=2p\), the weaker condition \(p\ge18h\) suffices.
The hypothesis also implies \(m\le u\): from (3),
\(2(u-m)\ge p(p-1)-(p+q)h\ge p(p-1)-(3p+1)h\ge0\).
Thus the lower bound attained here is exactly the corresponding case of the
Erdős–Faudree–Ordman bound.

The formula keeps track of the three kinds of modification separately. In this region,
removing a core edge raises the reference expression by one, removing a crossing edge
lowers it by one, and adding an exterior edge lowers it by two. The constants in the
local hypotheses are sufficient constants from the construction; their optimality is
not asserted.

**Theorem B (restriction to triangles).** Under (4),
\[
\operatorname{cp}_{\le3}(G)=s-u-m=M(n)+C-A-m, \tag{6}
\]
and hence
\[
\operatorname{cp}_{\le3}(G)-\operatorname{cp}(G)=m. \tag{7}
\]

Thus even an optimal triangle construction loses one block per exterior edge relative
to the unrestricted optimum. This compares two permitted block families. Within the
triangle packing problem itself, both the integral and fractional optima equal \(u+m\),
as shown in Section 4.

**Theorem C (prescribed exterior blocks).** If
\[
p\ge63h, \tag{8}
\]
then for every function \(\sigma:E(H)\to\{4,5\}\), there
is an optimal partition in which each exterior edge \(xy\) lies in a block
\(K_{\sigma(xy)}\) containing exactly two exterior vertices. Every other block is a
triangle of type \((2,1)\) or a crossing single edge. If \(k=|\sigma^{-1}(5)|\), its
block counts are
\[
N_5=k,\quad N_4=m-k,\quad N_3=u-m-2k,
\quad N_2=s-2u-2m+2k. \tag{9}
\]
In particular, \(G\) has at least \(2^m\) distinct optimal clique partitions.

The prescription may vary from edge to edge. The theorem constructs a partition for
each prescription. Section 9 distinguishes this freedom from the bounded recourse
available in a particular lifting layer.

For complete joins, the all-\(K_5\) case permits a further conclusion about
the optimal partitions themselves. Section 10 extends every legal terminal prefix,
controls the full partition after a lifting change, and connects the bounded-load
all-\(K_5\) optima by bounded steps. These statements keep the complete-join and
all-\(K_5\) hypotheses; they do not concern the whole mixed-prescription class.

### 1.3. Proof strategy and earlier work

Erdős, Faudree and Ordman [EFO88] proved that a bipartition with \(u,v\) internal edges
and \(s\) crossing edges satisfies
\(\operatorname{cp}(G)\ge s-u-v-\min\{u,v\}\). They also identified the efficiency of
blocks \(K_4\) and \(K_5\) with two vertices on one side. We use an asymmetric form of
their bound whose zero-slack types are precisely
\((1,1),(2,1),(2,2),(3,2)\). The contribution considered here is a uniform construction
attaining that bound throughout the stated local neighborhood, including missing core
and crossing edges and arbitrary exterior-edge prescriptions.

The construction has two stages. First, each exterior edge is extended to a suitable
clique. A bound on the number of extensions using any core vertex keeps enough crossing
edges available. Second, the residual core is decomposed into triangles by choosing an
exterior vertex for each residual edge. This is a list edge-coloring problem: the list
for a core edge consists of exterior vertices whose two crossing edges remain available.
The theorem of Häggkvist and Janssen [HJ97] completes this step exactly.

The independent-join case has a stronger classical antecedent. Pullman and Donald [PD81, Theorem 3], cited here through
[EFO88, p. 94] and [WZ93, Corollary 3.3], proved that
\[
\operatorname{cp}(F\vee I_q)=q|V(F)|-e(F)
\quad\text{if }q\ge\chi'(F),
\]
and described its optimal partitions by edges and triangles. The factor \(I_q\)
is independent. This includes our case \(A=m=0\), even with an arbitrary core
graph \(F=G[P]\). It does not cover simultaneous missing crossing edges and
added exterior edges. Wallis and Zhang [WZ93, Proposition 3.2] give an exact characterization
of the clique partition number of an independent join through a generalized
clique-coloring optimization. Their Corollary 3.3 gives the if-and-only-if criterion
for the preceding equality and attributes it to Pullman and Donald. It also
recovers a boundary case of Theorem D: when the exceptional vertex is adjacent
to every ordinary exterior vertex, moving that vertex into the core gives an
independent join to which the classical criterion applies. These are exact
antecedents in the join subfamilies; they do not supply the simultaneous-edit
construction or the prescribed exterior liftings considered here.

Erdős, Ordman and Zalcstein [EOZ93] posed the chordal clique-partition problem
and exhibited complete-split extremal examples. Chen, Erdős and Ordman
[CEO94, Theorems 1–2] proved the bounds \(3n^2/16+O(n)\) for split graphs
and \(n^2/6+O(n)\) for complete split graphs. Their use of core matchings,
triangular completions and accounts for missing crossing edges is an antecedent
of the construction method. Our assertion is a finite equality under the stated
local hypotheses, rather than a bound for every split graph. In Section 8,
the exceptional family is split when \(a=p\); the general family also includes
nonchordal graphs. Wallis and Wu [WW91] proved NP-completeness for the general
split-graph problem, consistent with the restricted recognition result here.
The subfamily \(a=p\) is also threshold. Ma's degree-class bounds
[Ma88, Theorem 2] already attain the integral value in a subregion of that family:
when the core is nonempty, the exceptional vertex has more exterior neighbors than the core size and
at least the core size of exterior nonneighbors. Theorem D treats the full
exceptional family and also determines its fractional and triangle optima.
This comparison uses the full Chinese article, rather than only its abstract.

Related terminal constructions appear in Okechukwu [Oke26, Lemmas 4.1–4.3]. Its Lemma 4.2 gives a triangle-partition upper bound under its own coloring, capacity and defect hypotheses. In clean-crossing subcases satisfying those hypotheses, the upper bound matches the elementary lower bound used in B. This comparison does not cover the full simultaneous-edit window of B. Ning [Nin26, Proposition 3.1]
attains the EFO bound using \(K_4\)'s for joins of two specified unions of
equal cliques, under its parity and size conditions. General effects of deletions
on the clique partition number were studied by Monson [Mon96]. The lower bounds,
efficient block types, independent-join formula and core-matching method are
classical inputs.

Enumeration of minimum edge-clique partitions also has classical antecedents:
McGuinness and Rees [MR90] enumerate them for line graphs. More generally,
Kwan, Sah and Sawhney [KSS23] count complete-graph clique decompositions without
the minimum-block restriction used here. Theorem E instead gives a uniform
lower bound for every prescribed exterior-block pattern in our local region.
List-edge-coloring reconfiguration has its own established theory [IKD12].
Section 10 controls full clique partitions in a bounded-load all-K5 class,
with bounded block changes; it is not a general single-edge-recoloring result.
These comparisons identify the scope of the contributions and do not
constitute an exhaustive historical-priority claim.

Section 2 gives the lower-bound certificate and the completion tool. Sections 3–5
prove A, B and C. Sections 6–7 derive local chordal stability and fractional
optimality. Section 8 recovers the core and determines the exceptional-vertex defect;
Section 9 states the counting result. Section 10 proves stable completion and
restricted connectivity for complete joins with all-\(K_5\) liftings.
The appendices give an elementary join
construction, a localization of inefficient blocks, and the counting proof.

## 2. Lower bounds and exact completion

### 2.1. A slack identity

For a clique of type \((a,b)\), with \(a+b\ge2\), define
\[
\ell(a,b)=1-ab+\binom a2+2\binom b2
=\frac{(a-b)(a-b-1)+(b-1)(b-2)}2\ge0. \tag{10}
\]
The inequality follows because a product of consecutive integers is nonnegative.
For any clique partition \(\Pi\), counting each present edge once gives
\[
|\Pi|-(s-u-2m)=\sum_{Q\in\Pi}\ell(a_Q,b_Q). \tag{11}
\]
Consequently \(\operatorname{cp}(G)\ge s-u-2m\) for every graph with the fixed
bipartition, without a restriction on \(h\). This follows also from [EFO88] and
coincides with its bound when \(m\le u\).

The identity counts the same physical edges in two ways. A crossing edge appears
once in the term involving \(ab\), a core edge once in the term involving
\(\binom a2\), and an exterior edge once in the term involving
\(\binom b2\). The remaining contribution is one per block. No choice of a
particular construction is used in this lower bound.

Both products in (10) vanish exactly for
\[
(a,b)\in\{(1,1),(2,1),(2,2),(3,2)\}. \tag{12}
\]
It is therefore enough to construct a partition using only these types. The identity
will also identify all optimal types once such a partition has been constructed.

### 2.2. Available core pairs and triangles

Let \(B\) be a graph of forbidden pairs in the core, with \(\Delta(B)\le D\).
Any candidate set of at least \(D+2\) vertices contains an available pair. Indeed,
one vertex forbids at most \(D\) others. A candidate set of at least \(2D+3\)
vertices contains an available triangle: choose an available pair and then a third
vertex outside its two endpoints and their forbidden neighborhoods. At most
\(2D+2\) vertices have been excluded.

### 2.3. Completion by list edge coloring

Häggkvist and Janssen [HJ97] proved
\[
\chi'_{\ell}(K_p)\le p. \tag{13}
\]
We apply this to a residual core graph \(J\subseteq G[P]\). For each \(a\in P\),
let \(F_a\subseteq O\) consist of exterior vertices whose crossing edge to \(a\)
is absent or has already been used. Give each \(ab\in E(J)\) the list
\(L_{ab}=O\setminus(F_a\cup F_b)\).

If every list has at least \(p\) elements, extend the lists to the abstract complete
graph on \(P\) by assigning \(O\) to every nonresidual pair. These added lists have
size \(q\ge p\), so (13) applies. Restrict the resulting proper list coloring to
\(E(J)\). An edge \(ab\) of color \(x\) gives the triangle \(abx\). The lists
ensure that both crossing edges exist and are unused; properness ensures that no
two of the new triangles use the same crossing edge. The fictitious core pairs
are not made into blocks. Once the exterior and core edges have all been covered,
the remaining crossing edges can be taken individually.

### 2.4. Other core sizes

The lifting argument does not require \(p=\lfloor(n+1)/3\rfloor\). For an
arbitrary reference split graph with part sizes \(p,q\), let \(h\) have the
same local meaning as before.

**Proposition 2.1.** Let \(t\ge1\) be an integer. If
\[
p+(4t+2)h\le q,\qquad q+t(t+5)h\le tp,
\]
then
\[
\operatorname{cp}(G)=\operatorname{cp}_{\le4}(G)
=s-u-2m=pq-\binom p2+C-A-2m.
\]

*Proof.* Use the construction of Section 3 with load cap \(r=th\).
For \(h\ge1\), the candidate and pair selection is valid whenever
\[
r(5h+r-2)+2(m-1)\le rp.
\]
The second size inequality and \(2m\le qh\) imply this capacity bound.
The first size inequality is exactly the list condition
\(p+2(h+2r)\le q\). Thus the same physical construction gives only zero-slack
blocks and attains the lower bound. If \(h=0\), there is no exterior lifting,
and list coloring completes the complete core since \(q\ge p\). ∎

For example, \(t=4\) permits
\(p+18h\le q\le4p-36h\). This also covers the second complete-split
extremal size. At \(n=3k+1\), both
\[
K_k\vee I_{2k+1},\qquad K_{k+1}\vee I_{2k}
\]
have baseline \(M(n)\). For the second core, of size \(p=k+1\), the sufficient
condition \(p\ge18h+2\) gives the same formula \(M(n)+C-A-2m\).
Indeed \(q=2p-2\) satisfies the displayed window, and
\(p(2p-2)-\binom p2=M(3p-2)\). The local equality assertion in Section 6
is always relative to its specified reference graph.


## 3. Proof of Theorem A

If \(h=0\), then \(G=S\). A proper coloring of the core edges with at most \(p\)
exterior colors gives the required triangle construction. One such coloring labels
the core by \(\mathbb Z/p\mathbb Z\) and colors \(ab\) by \(a+b\); incident edges
have distinct colors. For \(p=1\) there are no core edges. The resulting partition
has \(pq-\binom p2=M(n)\) blocks and attains (11).

Assume \(h\ge1\). Process the exterior edges \(xy\in E(H)\) in any order, assigning
an available core pair \(ab\) to obtain a \(K_4\) on \(\{a,b,x,y\}\). Maintain
that core pairs are never reused, that the core pairs assigned to incident exterior
edges are vertex-disjoint, and that every core vertex belongs to at most \(r=4h\)
assigned blocks. Call the number of assigned blocks containing a vertex its load.

Before processing \(xy\), exclude core vertices nonadjacent to \(x\) or \(y\),
vertices used earlier at either exterior endpoint, and vertices of load \(r\).
The first two causes exclude at most
\[
\beta_x+\beta_y+2(d_H(x)-1)+2(d_H(y)-1)\le4h-4. \tag{14}
\]
The total load before this step is at most \(2(m-1)\), so fewer than
\(2m/(4h)\le q/4\) vertices are saturated. The candidate set has size \(k\) with
\[
\begin{aligned}
k&>p-4h+4-q/4\\
 &\ge p/2-4h+15/4\\
 &\ge5h+17/4,
\end{aligned} \tag{15}
\]
using \(q\le2p+1\) and (4).

Here a saturated vertex has load exactly \(r\). Each previously assigned
exterior edge contributes two units to total core load, which bounds the number
of saturated vertices. The other exclusions are estimated by a union bound;
they need not be disjoint. The joint inequalities in (3), rather than separate
worst-case bounds for missing edges and exterior degrees, give (14).

The forbidden-pair graph consists of missing core edges and previously used core
pairs. Its maximum degree is at most \(h+r=5h\). Section 2.2 and (15) therefore
give an available pair \(ab\). The four crossing edges of \(abxy\) are present and
free by the exclusions, and \(xy\) is the current exterior edge. Since \(a,b\)
were not saturated, their new loads remain at most \(r\). This proves the induction.
If \(m=0\), this stage is empty.

At the end, a core vertex \(a\) of load \(t_a\le4h\) has used exactly \(2t_a\)
distinct crossing edges. Hence \(|F_a|=\alpha_a+2t_a\le9h\), and every residual
core edge has a list of size
\[
|L_{ab}|\ge q-18h\ge2p-1-18h\ge p. \tag{16}
\]
Section 2.3 completes the \(u-m\) residual core edges with triangles. The \(m\)
blocks \(K_4\) use \(4m\) crossing edges, and the triangles use \(2(u-m)\).
There remain \(s-2u-2m\) crossing single edges. The total number of blocks is
\(s-u-2m\), attaining (11). Their counts are nonnegative because they count the
blocks of this partition.

The incident-edge invariant is also what makes the calculation of \(F_a\)
exact: two lifting blocks through the same core vertex cannot use the same
exterior endpoint. Thus the \(2t_a\) crossing edges counted there are distinct,
and the subsequent list coloring cannot reuse any of them.

When \(q=2p\), the candidate estimate has more room and the last inequality in
(16) requires only \(p\ge18h\). This proves the balanced variant. ∎

## 4. Proof of Theorem B

Every triangle has at least one edge internal to one of the two parts. There are
\(u+m\) such edges, so a triangle packing has size at most \(u+m\).

To see the injection behind this bound, choose one internal edge from each
triangle. Different triangles of the packing cannot choose the same edge because
the packing is edge-disjoint. The later fractional argument is a separate weighted
version of this count; it does not assume that a fractional packing is integral. A partition
with \(t\) triangles and all remaining edges individual has \(e(G)-2t\) blocks.
Therefore
\[
\operatorname{cp}_{\le3}(G)\ge(s+u+m)-2(u+m)=s-u-m. \tag{17}
\]

We construct \(u+m\) triangles. The case \(h=0\) was handled in Section 3.
For \(h\ge1\), first process each exterior edge \(xy\), assigning a core root
\(a\) to form \(axy\). Allow each core root to receive at most \(2h\) exterior
edges. Missing adjacencies and previous assignments at \(x,y\) exclude at most
\[
(\beta_x+d_H(x)-1)+(\beta_y+d_H(y)-1)\le2h-2
\]
roots. Fewer than \(m/(2h)\le q/4\) roots are saturated. There remain more than
\[
p-(2h-2)-q/4\ge p/2-2h+7/4>0
\]
candidates, so the assignment can be completed.

This stage covers all exterior edges and uses no core edge. Each core vertex has
used at most \(4h\) crossing edges. Including its missing adjacencies, it forbids
at most \(5h\) exterior colors. Every core-edge list thus has size at least
\(q-10h\ge p\). Section 2.3 provides one triangle for each of the \(u\) core
edges, reaching \(u+m\) triangles and equality in (17). Together with A this proves
(7). ∎

The root selection must use the missing-adjacency information. An ordinary coloring
of \(H\) followed by an arbitrary assignment of colors to core vertices would not
ensure that all required crossing edges exist.

The same internal-edge count is a fractional certificate: give weight one to every
internal edge and zero to every crossing edge. Every triangle has total covering
weight at least one. The constructed packing attains its value, so
\[
\nu_3(G)=\nu_3^*(G)=u+m. \tag{18}
\]

## 5. Proof of Theorem C

When \(h=0\), the prescription is empty, and the base construction applies. Assume
\(h\ge1\) and fix \(\sigma\). A prescribed \(K_4\) needs a core pair, whereas a
prescribed \(K_5\) needs a core triangle. As before, require the core edges used in
different blocks to be distinct, and the core sets assigned to incident exterior
edges to be vertex-disjoint. Set the maximum vertex load to \(r=7h\).

Before processing \(xy\), missing crossing edges and previous assignments at its
endpoints exclude at most
\[
\beta_x+\beta_y+3(d_H(x)-1)+3(d_H(y)-1)\le6h-6
\]
vertices. The total previous load is at most \(3(m-1)\), so fewer than
\(3m/(7h)\le3q/14\) vertices are saturated. The number of candidates is greater than
\[
\begin{aligned}
p-6h+6-3q/14
&\ge4p/7-6h+81/14\\
&\ge30h+81/14>30h+3.
\end{aligned} \tag{19}
\]
Each earlier participation used at most two incident core edges. Including missing
core edges, the forbidden-pair graph has maximum degree at most \(h+2r=15h\).
Section 2.2 gives an available core triangle. Use all of it for label 5 and only
one of its pairs for label 4, charging just the vertices actually used. The same
exclusions as in Section 3 ensure that all block edges are present, unused, and
consistent with the invariants.

A triple is used only to find an available configuration. For a prescribed
\(K_4\), its unused third vertex is not added to the lifting and receives no
load. For a \(K_5\), a participation uses two incident core edges; this is why
the forbidden-pair degree is bounded by \(h+2r\) in the next step.

At the end, every core vertex has used at most \(2r=14h\) crossing edges. The
completion lists have size at least
\[
q-2h-4r=q-30h\ge2p-1-30h\ge p,
\]
since \(p\ge63h\) and \(h\ge1\). Apply Section 2.3 and leave the remaining crossing
edges as single-edge blocks. Every block has zero slack in (11), proving optimality.

If \(k\) exterior edges have label 5, the large blocks use \(m+2k\) core edges and
\(4m+2k\) crossing edges. Thus \(N_3=u-m-2k\) and
\[
N_2=s-(4m+2k)-2(u-m-2k)=s-2u-2m+2k,
\]
which proves (9). Finally, the order of the unique block containing any exterior
edge recovers its label. Distinct prescriptions therefore yield distinct partitions,
giving at least \(2^m\) optima. ∎

## 6. Local stability for chordal graphs

**Lemma 6.1 (core rigidity).** Under the hypotheses of A, if \(G\) is chordal, then
\(C=0\).

*Proof.* The case \(h=0\) is immediate. Otherwise suppose that a core edge \(ab\)
is missing. Its endpoints have at least
\[
q-\alpha_a-\alpha_b\ge q-2h\ge2p-1-2h>h+1
\]
common exterior neighbors. Since \(\Delta(H)\le h\), this set is not a clique.
Choose nonadjacent common neighbors \(x,y\). The vertices \(a,x,b,y\) induce a
cycle of length four: its two possible chords \(ab,xy\) are absent. This contradicts
chordality. ∎

Consequently A gives, for chordal graphs in this neighborhood,
\[
\operatorname{cp}(G)=M(n)-A-2m. \tag{20}
\]
The labeled edit distance is \(d_{\rm edit}=|E(G)\triangle E(S)|=A+m\). Hence
\[
d_{\rm edit}\le M(n)-\operatorname{cp}(G)\le2d_{\rm edit}. \tag{21}
\]
In particular, equality \(\operatorname{cp}(G)=M(n)\) forces \(G=S\) within this
neighborhood. This is a local conclusion relative to the fixed reference graph;
it does not characterize all extremal chordal graphs.

## 7. Fractional optimality and the types of optimal blocks

Define the fractional partition number \(\operatorname{cp}_{=}^{*}(G)\) by minimizing
\(\sum_Q x_Q\), over cliques of order at least two, subject to
\(x_Q\ge0\) and \(\sum_{Q\ni e}x_Q=1\) for every present edge \(e\).
Give present crossing, core and exterior edges respective weights \(1,-1,-2\).
Their sum on a clique of type \((a,b)\) is \(1-\ell(a,b)\le1\), and their total
sum is \(s-u-2m\). Thus every feasible fractional partition satisfies
\[
\sum_Qx_Q-(s-u-2m)=\sum_Q\ell(a_Q,b_Q)x_Q\ge0.
\]
Under A the integral construction attains the bound, proving
\[
\operatorname{cp}_{=}^{*}(G)=\operatorname{cp}_{\le4,=}^{*}(G)
=\operatorname{cp}_{\le4}(G)=\operatorname{cp}(G). \tag{22}
\]
Here the subscript \(\le4\) restricts the fractional block variables as well.
This is equality for the uniform partition objective; it does not assert that the
whole polytope is integral. The edge constraints are equalities, so this is also
different from the fractional covering problem.

Equivalently, maximize the gain \(\binom{|Q|}{2}-1\) over edge-disjoint clique
packings, or over fractional packings with unit edge capacities. Completing unused
capacity by \(K_2\)'s shows that both gain optima are \(2u+3m\). This provides an
exact instance of the distinction in Paper V between a packing certificate and its
realization. The construction and lower bound here prove the equality directly;
no transfer theorem from Paper V is required.

Equation (11) also shows that every optimal integral partition uses only the four
types in (12). The same conclusion holds for the support of every optimal fractional
partition. No optimal block has order greater than five, even if the graph contains
larger cliques. Theorem A supplies an optimum using order at most four, while C
allows the stated independent choices between four and five. Appendix B quantifies
how many edges can lie in other types in a nearly optimal partition.

## 8. Recognizing the core and allowing one exceptional vertex

The formula in Theorem A is stated relative to a reference core. We first show that
the core can be recovered from the graph in that local region. We then examine a
family with one exceptional vertex. In that family the additional cost has an exact
formula, and changing the core need not remove it.

### 8.1. An intrinsic formula in the local region

For every vertex set \(Q\), without a condition on its size, put
\[
\Phi_Q(G)=e_G(Q,V\setminus Q)-e(G[Q])-2e(G[V\setminus Q]).
\]
The slack identity of Section 2 gives \(\Phi_Q(G)\le\operatorname{cp}(G)\) for
every \(Q\). Under the hypotheses of Theorem A, equality holds at the reference
core. Hence
\[
\operatorname{cp}(G)=\max_{Q\subseteq V}\Phi_Q(G)=\Phi_P(G).
\]
This conclusion does not assert uniqueness of the maximizing set.

If \(n\ge3\), the same hypotheses give the more useful identification
\[
P=\{v\in V:2d_G(v)>n\}.
\]
Indeed, a core vertex has degree at least \(n-1-h\), whereas an exterior vertex
has degree at most \(p+h\). For \(h=0\) the claimed separation follows from
\(n\ge3\) and the specified value of \(p\). For \(h\ge1\), use
\(p\ge18h+1\) and \(n\ge3p-1\) to obtain
\(n-1-h>n/2>p+h\).

Thus the value can be computed without receiving the reference partition: form the
set of vertices above this degree threshold, check its size and local modification
degree, and, if Theorem A applies, count its three edge classes. With an adjacency
matrix these operations take \(O(n^2)\) time. This is an algorithm for the value
on the recognized region. It does not supply a running-time bound for constructing
the partition through the sharp list-coloring theorem.

### 8.2. The exact exceptional-vertex defect

For this subsection, allow arbitrary sizes \(p,q\). Let \(P\) be a clique of
size \(p\), let \(R\) be an independent set of size \(q-1\), and include every
edge between \(P\) and \(R\). Add a vertex \(z\) with precisely \(a\) neighbors
in \(P\) and \(b\) neighbors in \(R\). Assume \(q\ge p+3\); zero values of
\(p,a,b\) are allowed when compatible with these conditions. Relative to the core
\(P\), write
\[
u=\binom p2,\qquad m=b,\qquad s=p(q-1)+a,\qquad \Phi=s-u-2b,
\]
and define
\[
D(a,b)=\max\{0,2b-a,3b-2a\}.
\]
The subfamily \(a=p\) is split. The general setup need not be chordal: if
\(a<p\) and \(b\ge2\), a nonneighbor of \(z\) in \(P\) and two neighbors
of \(z\) in \(R\) form an induced four-cycle with \(z\).

**Theorem D.** For this graph,
\[
\operatorname{cp}(G)=\operatorname{cp}_{\le4}(G)
=\operatorname{cp}^{*}_{=}(G)=\Phi+D(a,b).
\]
Moreover,
\[
\nu_3(G)=\nu_3^*(G)=u+\min(a,b),\qquad
\operatorname{cp}_{\le3}(G)-\operatorname{cp}(G)
=\min\{b,\max(0,a-b)\}.
\]
Here \(\operatorname{cp}^{*}_{=}\) denotes fractional partition with equality
on every edge, as in Section 7, and \(\nu_3\) counts edge-disjoint triangles.

*Proof.* Every block containing an edge from \(z\) to \(R\) contains exactly
one vertex of \(R\), the vertex \(z\), and some \(k\) neighbors of \(z\)
in \(P\). There are exactly \(b\) such blocks, since \(R\) is independent.
Their core sets are pairwise disjoint: sharing a core vertex would reuse its edge
to \(z\). Their total core size is therefore at most \(a\).

The slack of such a block is
\[
\ell(k,2)=3-2k+\binom k2\ge\max\{0,2-k,3-2k\}.
\]
All other blocks have nonnegative slack. Summation gives
\(\operatorname{cp}(G)\ge\Phi+D(a,b)\). The same bound is fractional.
To see this directly, start with the edge weights of Section 7. In addition to
these weights, use each of the two corrections
\[
(-1,2),\qquad (-2,3)
\]
on the edges \(zP,zR\), respectively. Each corrected weight is feasible for
every clique: the displayed inequalities handle blocks meeting \(R\), and the
correction is nonpositive on blocks through \(z\) meeting only \(P\). The three
dual values are \(\Phi,\Phi+2b-a,\Phi+3b-2a\).

This dual argument is needed for the fractional conclusion. Counting the
\(b\) actual blocks through \(zR\) proves the integral lower bound, but that
count alone would not justify a statement about arbitrary fractional weights.
Feasibility of the three edge-weight assignments provides the fractional lower
bound independently of the integral construction.

For the matching construction, assign disjoint subsets of the \(a\) core
neighbors of \(z\) to its \(b\) neighbors in \(R\). If \(a\le b\), use
\(a\) triangles and \(b-a\) individual edges through \(zR\). If
\(b\le a\le2b\), use \(a-b\) copies of \(K_4\) and \(2b-a\) triangles.
If \(a\ge2b\), use \(b\) copies of \(K_4\) and cover the unused \(zP\)
edges individually. These choices cover every edge incident with \(z\), and
their total slack is \(D(a,b)\).

Each core vertex has used at most one crossing edge to \(R\). Exclude \(z\)
from the completion colors. Each residual core edge then has at least
\(|R|-2=q-3\ge p\) available colors. The list-coloring completion of Section
2 covers the residual core by triangles; all remaining crossing edges are individual
blocks. Those final blocks have zero slack. This constructs an optimum of order
at most four, and its indicator also attains the fractional bound.

For triangles, give covering weight one to every core edge and, according to
which set is smaller, to all \(zP\) or all \(zR\) edges. Every triangle receives
weight at least one. The covering weight is \(u+\min(a,b)\), proving the
fractional upper bound. Use \(\min(a,b)\) triangles through \(z\) with distinct
core and exterior neighbors. Complete all \(u\) core edges with colors in \(R\),
again using lists of size at least \(p\). This attains the covering weight.
Finally, a triangle packing of size \(t\) completes to \(e(G)-2t\) pieces.
Substitution of the two exact formulas, in the three ranges for \(a\), gives
the stated restriction gap. ∎

### 8.3. What changing the core cannot repair

The exceptional family already obstructs larger local ranges. Take \(a=p\)
and \(b=\lfloor p/2\rfloor+1\), with \(p\ge1\) and the standing assumption \(q\ge p+3\) from Section 8.2. The graph is split, hence
chordal, and its modification degree relative to the original core is \(h=b\).
Its defect is \(D(p,b)=2b-p>0\). Thus a defect-free formula for every chordal
perturbation cannot extend to modification ratios strictly beyond \(1/2\).
This gives an upper obstruction; a matching sufficient threshold is not proved.
For the choice \(q=2p\), which requires \(p\ge3\) under this standing assumption, the exceptional vertex satisfies
\(d_G(z)=p+b>n/2\). The degree test of Section 8.1 would place it in the core,
but its local hypotheses fail: relative to \(P\cup\{z\}\), the vertex \(z\)
has \(2p-1-b\) missing crossing edges.

One might try to remove the defect by changing the reference core. Even optimizing
over every bipartition can fail. If \(q=2p\) and \(p\ge19\), then
\[
\max_{Q\subseteq V}\Phi_Q(G)=\Phi+\max\{0,3b-2a\}.
\]
Here is a direct comparison. For a proposed \(Q\), put
\(x=|Q\cap P|\), \(x'=p-x\), \(y=|Q\cap R|\), and
\(y'=2p-1-y\). The normal vertices contribute at least
\[
2\left(\binom x2+xy\right)
+3\left(\binom{x'}2+x'y'\right)
\ge 2\binom p2+3x'+3y
\]
to \(2e(G[Q])+3e(G[V\setminus Q])\). To check the inequality, twice its
difference is
\(E=5x'^2+(8p-13)x'+(4p-6)y-10x'y\), and
\[
\begin{aligned}
(2p-1)E&=(2p-1-y)\bigl(5x'^2+(8p-13)x'\bigr)\\
&\quad+y\bigl(p^2+2px+5x^2-19p+3x+6\bigr)\ge0.
\end{aligned}
\]
The condition \(p\ge19\) is used here through \(p^2-19p\ge0\);
it is a sufficient condition for this estimate.
If \(z\in Q\), at least \(a-x'\) of its core neighbors lie in \(Q\),
giving total cost at least \(2\binom p2+2a\). If \(z\notin Q\), at least
\(b-y\) of its neighbors in \(R\) lie outside \(Q\), giving cost at least
\(2\binom p2+3b\). Since \(\Phi_Q=e(G)-2e(G[Q])-3e(G[V\setminus Q])\),
these bounds give the asserted maximum. It is attained by \(P\) or
\(P\cup\{z\}\), whose values differ by \(3b-2a\).

For \(a=p\) and \(0\le b\le p\), the gap is
\[
\operatorname{cp}(G)-\max_Q\Phi_Q(G)
=\max\{0,2b-p\}-\max\{0,3b-2p\}.
\]
It is already positive when \(p/2<b<2p/3\). The value \(2p/3\) marks the
change between the two maximizing reference cores and the peak of the piecewise-linear
gap expression, rather than the onset of failure after optimizing the core.
In particular, for \(a=p\), \(3b=2p\), and \(p\ge19\),
\[
\operatorname{cp}(G)-\max_Q\Phi_Q(G)=p/3.
\]
Every modification is incident with \(z\); every other vertex has modification
degree at most one. Taking \(p=3t\), \(t\ge7\), gives concrete chordal examples
with gap \(t\). A bounded number of exceptional vertices therefore cannot be
treated as a constant additive cost without another hypothesis. The three duals
of Theorem D detect a resource obstruction that the bipartition family alone misses.
In Paper V's terminology, the competing exterior demands share the finite set
of usable edges from \(z\) to the core; small total edit distance does not
bound the resulting realization loss.

## 9. Prescriptions and the number of optimal partitions

Let \(N(G)\) count clique partitions of the labeled graph \(G\) attaining
\(\operatorname{cp}(G)\). Partitions are families of vertex sets, rather than
ordered lists of blocks or isomorphism classes.

**Theorem E.** Under the hypotheses of Theorem C, if \(p\ge16\), each fixed
exterior-edge prescription is realized by at least
\(p^{\lfloor p^2/64\rfloor}\) optimal partitions. Consequently,
\[
2^m p^{\lfloor p^2/64\rfloor}\le N(G)\le(n+1)^{5e(G)}.
\]
In particular, \(\log N(G)=\Theta(p^2\log p)\) along this region as
\(p\to\infty\).

The proof, given in Appendix C, fixes the exterior lifting and counts many compatible
colorings of a substantial sparse subgraph of the residual core. Vizing's theorem
extracts that subgraph; Häggkvist–Janssen extends every counted prefix. These two
coloring results have different roles. The residual core has degree close to \(p\),
so treating it as a graph of degree \(O(h)\) would not justify the conclusion.

The lifting also permits a bounded change when a physical exterior block is
prescribed. We give the invariant and argument, since this conclusion concerns
more than the choice of block orders.

For an exterior edge \(e=xy\), a *legal core set* is a subset \(N\subseteq P\) that induces a clique and whose every vertex is adjacent to both \(x\) and \(y\). Legality here concerns that single proposed block; compatibility with the current lifting is imposed or repaired separately.

**Proposition 9.1 (extension and exterior recourse).** Assume Theorem C's hypotheses.
For each assigned exterior edge \(e=xy\), let \(T_e\subseteq P\) have size two
or three, induce a clique, and be joined to both endpoints of \(e\). Require that
the core edge sets of the \(T_e\) are pairwise disjoint, that
\(T_e\cap T_f=\varnothing\) whenever \(e,f\) are distinct incident exterior
edges, and that each core vertex belongs to at most \(7h\) assigned sets.
Any such partial lifting extends to an optimal partition with the specified
orders on all exterior edges, provided these orders agree with the assigned sets.
Given a complete lifting and a new legal core set
\(N\) of size two or three for one edge \(e_0\), there is a complete lifting
containing \(N\) at \(e_0\) which changes at most thirteen assignments,
including that at \(e_0\), and retains the load bound. Only the order prescribed
at \(e_0\) may change.

*Proof.* The estimates of Section 5 depend on the number of edges assigned and
the stated invariant, so its induction may start from the prescribed partial
lifting. The list-coloring completion then preserves every assigned block.

For recourse, remove the old assignment at \(e_0\). Also remove every assignment
using a pair in \(N\), or using a vertex of \(N\) at an endpoint of \(e_0\).
Each of the at most three pairs in \(N\) has at most one owner, by core-edge
disjointness. Each of the at most six endpoint–core incidences has at most one
owner, by the incident-edge condition. After these removals, if a vertex of
\(N\) still has load \(7h\), remove one further assignment containing it.
At most three additional removals suffice. Thus at most
\(1+3+6+3=13\) exterior assignments have been removed. Since \(e_0\) is an
exterior edge, \(h\ge1\), so a saturated vertex has an assignment available
to remove. Insert the new block: it has no pair or crossing-edge conflict, and
its core vertices had load below \(7h\). Extend the resulting partial lifting
by the first assertion. All assignments outside the removed set are preserved. ∎

The triangle completion may change globally. Proposition 9.1 bounds changes in
the exterior lifting layer; it does not imply a thirteen-block change in the
whole partition or connectivity of arbitrary optimal partitions.
The complete-join all-\(K_5\) subclass admits the stronger conclusions of Section 10.

The role of the series is now more explicit. Paper IV [IV] uses structural
localization and physical terminal accounts to pay the global partition budget.
The present results determine exact optima and the cost of a restricted terminal
family in a local region, while Theorem D identifies an additional obstruction
when local control fails. Paper V [V] provides a language for charging realization
losses, but its abstract transfer inequality does not construct the root or the
cheap realizations used here. None of these local conclusions is inferred merely
from a small total edit distance.


## 10. Stable completion and restricted connectivity in complete joins

The exterior recourse of Proposition 9.1 controls assignments, while a clique
partition also contains terminal triangles and crossing single edges. In a complete
join with all exterior blocks of order five, these remaining blocks can be repaired
with a cost proportional to the number of changed assignments. The reason is an
exact compensation between the core edges and crossing edges used by a lifting.

Throughout this section let \(p\ge1\), let \(G=K_P\vee H\), where
\(|P|=p\), \(|V(H)|=q\), and write \(u=\binom p2\), \(m=e(H)\).
A *legal complete all-\(K_5\) lifting* assigns to each exterior edge \(xy\) a
core triple \(T_{xy}\), with the resulting blocks \(T_{xy}\cup\{x,y\}\)
pairwise edge-disjoint. Its load at a core vertex is the number of these blocks
containing that vertex. A terminal triangle has type \((2,1)\).

### 10.1. Completion from an arbitrary legal prefix

**Lemma 10.1.** Suppose \(q\ge2p-1\), and fix a legal complete all-\(K_5\)
lifting. Every family of edge-disjoint terminal triangles avoiding its blocks
extends to an optimal clique partition containing the lifting. The remaining
blocks are terminal triangles and crossing single edges.

*Proof.* Let \(J\) be the unused core graph and \(F_a\) the exterior vertices
whose crossing edges at \(a\) are used by the lifting. If \(a\) has load
\(t_a\), edge-disjointness gives
\[
d_J(a)=p-1-2t_a,\qquad |F_a|=2t_a,
\qquad d_J(a)+|F_a|=p-1.
\]
The prescribed terminal triangles give a proper partial edge coloring of \(J\),
with exterior vertices as colors. The color on \(ab\) avoids
\(F_a\cup F_b\). For an uncolored edge \(ab\), the lifting and the colors
already used at its endpoints forbid at most
\[
|F_a|+|F_b|+(d_J(a)-1)+(d_J(b)-1)=2p-4<q
\]
colors. Thus every remaining edge can be colored greedily without changing the
prefix. If an uncolored edge exists, then \(p\ge2\) and both endpoint degrees
are positive, so the count has no negative degree term. Make the resulting colors
into terminal triangles and take the remaining crossing edges individually.
All blocks have zero slack in (11), proving optimality. In particular the block
counts are \(m\), \(u-3m\), and \(pq-2u\), respectively. ∎

The lemma assumes that the complete lifting already exists. It requires neither
a bound on its load nor an upper bound on \(q\). Its prefix may contain any
compatible terminal triangles, rather than just triangles selected by an earlier
execution of the greedy procedure.

### 10.2. Repairing the whole partition

**Proposition 10.2.** Suppose \(q\ge2p-1\). Let \(L_0,L_1\) be legal complete
all-\(K_5\) liftings whose assignments differ on exactly \(k\) exterior edges.
For every optimal clique partition \(\Pi_0\) extending \(L_0\), there is an
optimal partition \(\Pi_1\) extending \(L_1\) such that
\[
|\Pi_0\setminus\Pi_1|=|\Pi_1\setminus\Pi_0|\le34k,
\qquad |\Pi_0\triangle\Pi_1|\le68k.
\]
The partition \(\Pi_1\) can retain every terminal triangle of \(\Pi_0\) whose
edges avoid every block of \(L_1\).

*Proof.* Lemma 10.1 shows that the lower bound \(pq-u-2m\) is attained.
The slack identity therefore forces every optimal partition to use only the
zero-slack types. Since \(\Pi_0\) contains a lifting block for every exterior
edge, all its other blocks are terminal triangles or crossing single edges.
Its terminal family \(\mathcal T_0\) has \(u-3m\) members.

Keep the members of \(\mathcal T_0\) avoiding all blocks of \(L_1\), and let
\(R\) be the number discarded. An unchanged lifting block cannot meet an old
terminal triangle. Each changed new block has three core edges and six crossing
edges that can meet old terminal triangles. Since those triangles are
edge-disjoint, at most nine are discarded per changed assignment. Hence
\(R\le9k\). The retained triangles form a legal prefix for \(L_1\).
Both residual core graphs have \(u-3m\) edges, so Lemma 10.1 adds exactly
\(R\) terminal triangles to this prefix.

The residual core graphs need not have the same edge sets. Only their
cardinalities are compared: each retained triangle represents one distinct edge
of the new residual core, and every other such edge is a new request. This
explains why the number of requests to refill is exactly the number discarded.

At most \(k\) old lifting blocks and \(R\) old terminal triangles are lost.
An old crossing single edge can disappear only into a changed new lifting block
or a new terminal triangle. These use at most \(6k+2R\) crossing edges. Thus
\[
|\Pi_0\setminus\Pi_1|\le k+R+6k+2R
=7k+3R\le34k.
\]
The two optimal partitions have the same size, so their one-sided differences
are equal. Their sum gives the symmetric-difference bound. This also covers
\(k=0\), when the original partition is retained. ∎

For the bounded-load complete joins of Proposition 9.1, a legal new \(K_5\)
prescribed on one exterior edge can therefore be inserted while losing at most
\(34\cdot13=442\) old blocks and changing at most \(68\cdot13=884\) blocks
in symmetric difference. Unlike Proposition 9.1 alone, this controls the full
partition. The complete-join and all-\(K_5\) assumptions are used in Lemma 10.1.

### 10.3. Paths between bounded-load all-\(K_5\) optima

**Theorem 10.3.** Suppose
\[
q\in\{2p-1,2p,2p+1\},\qquad h=\Delta(H),\qquad p\ge63h.
\]
Let \(\mathcal C\) be the class of optimal clique partitions in which every
exterior edge belongs to a block \(K_5\) of type \((3,2)\), and the induced
lifting has load at most \(7h\) at every core vertex. Any two members of
\(\mathcal C\) are joined inside \(\mathcal C\) by a sequence of at most
\(u-2m\) steps, each of block symmetric difference at most \(884\).
More precisely, at most \(m\) steps change the exterior lifting; at most
\(u-3m\) further steps keep it fixed and have symmetric difference at most
\(18\).

*Proof.* Fix the target partition \(\Pi_*\) and its lifting \(L_*\).
First align the exterior assignments. Protect every assignment of the current
lifting already equal to its target. At an unaligned exterior edge \(e_0\),
prescribe the target triple \(N=L_*(e_0)\).

As in Proposition 9.1, remove the old assignment at \(e_0\), owners of core
pairs in \(N\), and owners of the crossing edges needed by the target block.
At most \(1+3+6\) assignments are removed. None is protected: a protected
owner would conflict with \(L_*(e_0)\) in the legal target lifting.
If a vertex of \(N\) remains saturated at load \(7h\), at most \(7h-1\)
of its assignments can be protected. Indeed the target lifting has load at most
\(7h\) there and also contains its additional assignment at \(e_0\).
There is therefore an unprotected assignment to remove. At most three further
removals leave room for the target block.

Insert that block and extend the retained partial lifting using Proposition 9.1.
All assignments remain of order five, the load bound is preserved, and at most
thirteen assignments change. Every protected assignment is retained, and
\(e_0\) becomes aligned. Proposition 10.2 supplies an optimal full partition
at block distance at most \(884\). At most \(m\) repetitions make the lifting
equal to \(L_*\). If \(m>0\), then \(h\ge1\), so the saturation threshold
used here is positive; if \(h=0\), this phase is empty.

Now keep this lifting fixed and align the terminal triangles. They are proper
list edge colorings of its residual core graph \(J\), and
\(|E(J)|=u-3m\). Protect every triangle already shared with \(\Pi_*\).
Choose an unaligned core edge \(ab\), whose target color is \(x\). Remove
its current triangle and the triangles, if any, on the at most two incident
edges currently colored \(x\). At most \(R\le3\) terminal triangles are
removed. None is protected, since the target coloring is proper.

Insert \(abx\). It avoids the lifting and every retained triangle, so
Lemma 10.1 completes this legal prefix while keeping all protected triangles.
At least one new target triangle is acquired. At most \(R\) old terminal
triangles are lost, giving terminal symmetric difference at most \(2R\).
Only the at most \(2R\) crossing edges in the new terminal triangles can
consume old crossing single edges. Both partitions have \(pq-2u\) crossing
single-edge blocks, so their symmetric difference is at most \(4R\).
The entire step therefore changes at most \(6R\le18\) blocks.

After at most \(u-3m\) steps all terminal triangles agree with the target.
The remaining crossing single edges are then forced, so the full partitions
agree. Concatenating the two phases gives at most
\(m+(u-3m)=u-2m\) steps. The inequality \(u\ge3m\) follows from the
edge-disjoint core triangles of any legal all-\(K_5\) lifting. ∎

The construction of Theorem C supplies members of \(\mathcal C\). For
\(p=1\) or \(2\), a complete all-\(K_5\) lifting forces \(m=0\); the first
phase is empty and the same terminal argument applies. The theorem concerns this
bounded-load all-\(K_5\) class. It gives neither connectivity of mixed
\(K_4/K_5\) optima nor recourse after arbitrary changes to the graph. No
optimality is claimed for the constants \(18\), \(68\), or \(884\).


**Formalization and reproducibility.** The companion [VI-companion] records the canonical Lean 4.35 entry point, theorem map, checked dependencies, final cached build and axiom audit for A–E, the intrinsic and exceptional results, and Section 10. Fractional partitions and triangle packings use real weights. Häggkvist–Janssen and Vizing are proved dependencies [HJ-formal, Viz-formal]. The final audit permits only Lean’s standard foundational axioms. Finite examples and independently checked certificates are regression evidence, separate from the universal proofs. The companion states their tested domains, proof dependencies and the scope of verification.

## Appendix A. An elementary complete-join variant

**Theorem A.1.** Let \(q\in\{2p-1,2p,2p+1\}\), \(n=p+q\), and
\(G=K_p\vee H\), where \(|H|=q\) and \(d=\Delta(H)\). If \(p\ge24d\), then
\[
\operatorname{cp}(K_p\vee H)=M(n)-2e(H). \tag{23}
\]
There is an optimum in which every exterior edge belongs to a \(K_5\) of type
\((3,2)\).

*Proof.* For \(d=0\), use the base construction. Assume \(d\ge1\) and put
\(m=e(H)\). Assign a core triangle to each exterior edge. Require the triangles
to be edge-disjoint, and vertex-disjoint when their exterior edges are incident.
Before processing \(xy\), previous uses at its endpoints exclude at most
\(6(d-1)\) core vertices. There remain
\(k\ge p-6(d-1)\ge3p/4+6\) candidates. At most \(3(m-1)\) core edges have been
used. Since
\(m\le qd/2\le p^2/24+p/48\),
\[
\begin{aligned}
\binom k2-3(m-1)-\left\lfloor k^2/4\right\rfloor
&\ge k^2/4-k/2-3m+3\\
&\ge p^2/64+29p/16+9>0.
\end{aligned} \tag{24}
\]
Mantel's bound gives an available triangle. For completeness, in a triangle-free
graph on \(k\) vertices the endpoints of every edge have degree sum at most \(k\).
Thus \(\sum_v d(v)^2\le ke\), whereas Cauchy–Schwarz gives
\(4e^2/k\le\sum_v d(v)^2\). For \(e>0\) this yields \(e\le k^2/4\), and the
case \(e=0\) is immediate. This justifies the selection in (24) and completes the
induction constructing all \(m\) blocks \(K_5\).

Let \(t_a\) be the number of these blocks containing a core vertex \(a\), and
let \(J\) be the residual core. Every participation uses two core edges and two
crossing edges at \(a\). Therefore
\[
d_J(a)=p-1-2t_a,\qquad |F_a|=2t_a,
\qquad d_J(a)+|F_a|=p-1. \tag{25}
\]
Now color \(E(J)\) greedily with exterior colors. When coloring \(ab\), the list
exclusions and earlier incident edges forbid at most
\[
|F_a|+|F_b|+(d_J(a)-1)+(d_J(b)-1)=2p-4
\]
colors. There are \(q\ge2p-1\) colors, so the choice is always possible.
Complete the core by triangles and take remaining crossing edges individually.
The counts are
\[
N_5=m,\qquad N_3=\binom p2-3m,\qquad N_2=pq-2\binom p2.
\]
Their sum is \(M(n)-2m\), attaining the lower bound. ∎

The value formula alone is already covered by Theorem A under the less restrictive
condition \(p\ge18d+1\). The additional content here is that every exterior edge
can use a \(K_5\) under \(p\ge24d\), rather than the general prescription
threshold \(63d\), and that completion is greedy and needs no HJ theorem.

Here the crossing colors spent by a \(K_5\) are compensated exactly by the decrease
in residual core degree. This permits greedy completion without the list-coloring
theorem used in the general perturbation setting.

## Appendix B. Edges in inefficient blocks

Under A, let \(\Pi\) be a partition with \(|\Pi|=\operatorname{cp}(G)+t\).
Equation (11) gives \(t=\sum_{Q\in\Pi}\ell(a_Q,b_Q)\). At most \(t\) blocks have
positive slack, and the union of their edges has size at most
\[
21t. \tag{26}
\]
To prove the latter bound, put \(k=a+b\). If \(k\le7\) and \(\ell(a,b)>0\),
integrality gives \(\binom k2\le21\le21\ell(a,b)\). If \(k\ge8\), use
\[
40\ell(a,b)=(10b-4k-1)^2+4k^2-28k+39
\]
to obtain
\[
21\ell(a,b)-\binom k2
\ge\frac{(k-8)(64k-56)+371}{40}>0.
\]
Summing proves (26). The constant is sharp for this blockwise inequality: type
\((4,3)\) has slack one and 21 edges. The bound localizes the inefficient blocks;
it does not imply a repair that leaves every other block fixed.

## Appendix C. Many completions for each prescription

Fix a prescription and one exterior lifting of Theorem C with load at most \(7h\).
Let \(J\) be the residual core and let \(L_e\) be its residual list at an edge
\(e\). Each core vertex has lost at most \(h\) original core neighbors and
at most \(14h\) core edges to the lifting. Therefore
\[
\delta(J)\ge p-1-15h,\qquad
e(J)\ge\frac{p(p-1-15h)}2.
\]
Its forbidden exterior set has size at most \(15h\), so \(|L_e|\ge q-30h\).

Put \(d=\lfloor p/8\rfloor\). Vizing's theorem [Viz64] colors \(J\)
properly with at most \(\Delta(J)+1\le p\) colors. Group consecutive colors
into windows of at most \(d\) colors. There are at most
\(\lfloor\Delta(J)/d\rfloor+1\le12\) windows for \(p\ge16\).
A largest window contains a subgraph with edge set \(K\), maximum degree at
most \(d\), and
\[
|K|\ge e(J)/12\ge p^2/64.
\]
For the last inequality, \(p\ge63h\) and \(p\ge16\) imply
\(p-1-15h\ge3p/8\).

Color the edges of \(K\) in a fixed order from their residual lists. An edge has
at most \(2(d-1)\) incident competitors in \(K\), and the size assumptions give
\[
q-30h-2(d-1)\ge p.
\]
Every step has at least \(p\) choices, independently of the preceding legal
choices. This counts at least \(p^{|K|}\) proper list-coloring prefixes.

For any such prefix, remove its incident colors from the lists of the uncolored
core edges. Each list loses at most \(2d\) additional colors and still has size
at least \(q-30h-2d\ge p\). Apply Häggkvist–Janssen as in Section 2 to complete
the residual core, retaining the prefix. Two prefixes give different partitions:
for each edge of \(K\), the unique triangle containing that core edge recovers
its exterior color. The exterior lifting is fixed throughout, so none of its blocks
uses an edge of \(K\). This proves the lower bound for a single prescription.

The families belonging to different prescriptions are disjoint, since the order
of the unique block through an exterior edge recovers its label. Multiplication
by \(2^m\) gives the total lower bound.

For the upper bound, every optimal block has order at most five, by the slack
identity. There are at most \((n+1)^5\) vertex sets of size at most five: list
their elements in a fixed order and pad with a sentinel to obtain an injective
encoding by five entries from an alphabet of size \(n+1\). A partition is
determined by the map assigning each edge its unique block. There are therefore
at most \(((n+1)^5)^{e(G)}\) optimal partitions.

Finally \(n=\Theta(p)\), \(e(G)=O(p^2)\), and the lower exponent is
\(\Theta(p^2)\). Taking logarithms gives the stated growth order. The formal
companion records the explicit finite bounds, without requiring a separate
asymptotic statement as a premise. ∎


## Acknowledgements

The author is deeply grateful to his wife María Paz and to his children Lucas,
Juan Cristóbal, Francisca, Raimundo and Benjamín for their love, patience and support.

## Use of artificial intelligence and computational tools

ChatGPT/Codex, by OpenAI, was used to explore and check arguments and to prepare the manuscript. Aristotle, by Harmonic, contributed to exploring approaches, searching for counterexamples, developing proofs, and formalizing and reviewing them in Lean; its role was not limited to translating finished proofs. Claude, by Anthropic, is credited in Paper IV for its contribution to the inherited work.

Certo [Certo] was used in the new finite checks. Earlier Certo and Jacobian [Jacobian] checks are retained in the accompanying audit materials, which identify their versions, specifications and recorded results. The finite certificates are checked separately from the construction that produces them. Their use is acknowledged separately from the logical dependencies of the formal proof. Computations were reviewed within their stated scope; a finite search does not replace a universal proof.

The source dossier records two AI construction reviews, one involving a participant in the derivations, and an algebraic audit. These are not independent human reviews.

The author remains responsible for the arguments, citations, code, and presentation. No AI system is listed as an author.

## References

[EFO88] P. Erdős, R. J. Faudree and E. T. Ordman, *Clique partitions and clique
coverings*, Discrete Mathematics **72** (1988), 93–101.
[Original article](https://www.renyi.hu/~p_erdos/1988-04.pdf).
[DOI](https://doi.org/10.1016/0012-365X(88)90197-5).

[HJ97] R. Häggkvist and J. C. M. Janssen, *New Bounds on the List-Chromatic Index
of the Complete Graph and Other Simple Graphs*, Combinatorics, Probability and
Computing **6** (1997), 295–313.
[DOI](https://doi.org/10.1017/S0963548397002927).

[Mon96] S. D. Monson, *The effects of vertex deletion and edge deletion on the
clique partition number*, Ars Combinatoria **42** (1996), 89–96.
[Original article](https://combinatorialpress.com/article/ars/Volume%20042/volume-42-paper-6.pdf).

[Oke26] O. Okechukwu, *Clique partitions and bounded simplicial defect*,
arXiv:2609.20871v1 (2026), especially Lemmas 4.1–4.3.
[Preprint](https://arxiv.org/html/2609.20871v1).

[Nin26] B. Ning, *On the difference between clique partition and clique covering
numbers of graphs*, arXiv:2608.11536v1 (2026), Proposition 3.1.
[Preprint](https://arxiv.org/html/2608.11536v1).


[Viz64] V. G. Vizing, *On an estimate of the chromatic class of a p-graph*,
Diskret. Analiz. **3** (1964), 25–30 (in Russian).

[IV] J. P. Traverso Gianini, *Clique partitions with rooted simplicial defect:
quantitative stability and sharp eventual bounds*, Paper IV, preprint v1.23 (2026).

[V] J. P. Traverso Gianini, *Colorability and Realizability Defects in
Resource-Dominated Packing Relaxations*, Paper V, Preprint 1.0 (2026).
[Public source and manuscript](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_V).

[PD81] N. J. Pullman and A. Donald, *Clique coverings of graphs—II:
complements of cliques*, Utilitas Mathematica **19** (1981), 207–213.
Cited through [EFO88, p. 94] and [WZ93, Corollary 3.3]; the original article
was not consulted for this review.

[EOZ93] P. Erdős, E. T. Ordman and Y. Zalcstein, *Clique partitions of
chordal graphs*, Combinatorics, Probability and Computing **2** (1993),
409–415. [DOI](https://doi.org/10.1017/S0963548300000808).

[CEO94] G.-T. Chen, P. Erdős and E. T. Ordman, *Clique partitions of split
graphs*, in Y. Alavi, D. R. Lick and J. Liu (eds.), *Combinatorics, Graph Theory,
Algorithms and Applications* (Beijing, 1993), World Scientific, 1994, 21–30.
[Author's copy](http://ordman.net/MathResearch/CEOClique_Parts.pdf).

[WW91] W. D. Wallis and J. Wu, *On clique partitions of split graphs*,
Discrete Mathematics **92** (1991), 427–429.
[DOI](https://doi.org/10.1016/0012-365X(91)90297-F).

[WZ93] W. D. Wallis and G.-H. Zhang, *On the partition and coloring of a
graph by cliques*, Discrete Mathematics **120** (1993), 191–203.
[DOI](https://doi.org/10.1016/0012-365X(93)90576-F).



[Ma88] S.-H. Ma, *Clique partitions of threshold graphs*, Acta Mathematicae
Applicatae Sinica **11** (1988), 493–502.
[Publisher](https://applmath.cjoe.ac.cn/jweb_yysxxb/EN/10.12387/C1988054). In Chinese, with an English abstract.

[MR90] S. McGuinness and R. Rees, *On the number of distinct minimal clique
partitions and clique covers of a line graph*, Discrete Mathematics **83** (1990),
49–62. [Author's copy](https://faculty.tru.ca/smcguinness/cliquecoverslinegraph.pdf).
[DOI](https://doi.org/10.1016/0012-365X(90)90220-C).

[KSS23] M. Kwan, A. Sah and M. Sawhney, *Enumerating Matroids and Linear Spaces*,
Comptes Rendus. Mathématique **361** (2023), 565–575.
[Published article](https://numdam.org/articles/10.5802/crmath.423/).

[IKD12] T. Ito, M. Kamiński and E. D. Demaine, *Reconfiguration of List
Edge-Colorings in a Graph*, Discrete Applied Mathematics **160** (2012),
2199–2207. [DOI](https://doi.org/10.1016/j.dam.2012.05.014).
The [WADS 2009 version](https://erikdemaine.org/papers/NPReconfiguration_WADS2009/paper.pdf)
is available from the authors.

[HJ-formal] J. P. Traverso Gianini, *The list chromatic index of complete graphs
(Häggkvist–Janssen)*, Lean formalization, Palomar
[PALOMAR-2026-10-15-000003, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000003&version=1).

[Viz-formal] J. P. Traverso Gianini, *Vizing's theorem and equitable edge
colourings*, Lean formalization, Palomar
[PALOMAR-2026-10-15-000004, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000004&version=1).

[VI-companion] J. P. Traverso Gianini, *Formalization and reproducibility companion
to Optimal Clique Partitions under Local Perturbations*, accompanying source
distribution, Preprint 1.0 (2026).
[Public source and companion](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_VI/05_formalization). Exact source and archive hashes are
recorded in the companion.

[Certo] J. P. Traverso Gianini, *Certo: computational tools with verifiable
certificates*. [Software](https://github.com/jtraverso/certo-math).
The audited local version and certificate specifications are fixed in the companion.

[Jacobian] Morluto and contributors, *Jacobian: composable mathematical tools*.
[Software](https://github.com/morluto/jacobian). Installed operation declarations
and versions used here are recorded with the computational checks.
