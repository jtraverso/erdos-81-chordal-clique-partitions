<div class="center">

Paper D in the series on clique partitions in split and chordal graphs. Preprint v0.3.

</div>

**Keywords.** Clique partitions; chordal graphs; split graphs; triangle packings; fractional packings; Erdős problems.

**MSC 2020.** 05C70, 05C35, 05C65, 05C69.

# Introduction

The edge clique partition number $\operatorname{cp}(G)$ is the minimum number of cliques whose edge sets partition $E(G)$. Erdős, Ordman and Zalcstein asked whether every $n$-vertex chordal graph admits an edge clique partition with $$\frac{n^2}{6}+O(n)$$ parts. The complete split graph $K_p\vee\overline{K}_{2p}$, $n=3p$, shows that the constant $1/6$ is the correct asymptotic barrier.

This preprint is the final step in the series. Paper A proves the sharp split graph theorem. Paper B develops the local and structural chordal toolkit. Paper C proves the fractional chordal theorem $$|E(G)|-2\nu_3^*(G)
    \le
    \left(\frac16+o(1)\right)n^2.$$ Here we combine that theorem with standard fractional-to-integral packing rounding for fixed graph families.

## Main result

<div id="thm:main" class="theorem">

**Theorem 1** (Chordal Clique Partition Theorem). *For chordal graphs, $$\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
    =
    \left(\frac16+o(1)\right)n^2.$$*

</div>

# Triangle packings and clique partitions

Let $\nu_3(G)$ denote the maximum number of edge-disjoint triangles in $G$, and let $\nu_3^*(G)$ denote the maximum total weight of a fractional triangle packing. Thus $$\nu_3^*(G)=
    \max\sum_{T\in K_3(G)}\psi_T$$ subject to $$\sum_{T\ni e}\psi_T\le1
    \qquad(e\in E(G)),
    \qquad
    \psi_T\ge0.$$

<div id="lem:packing-to-cp" class="lemma">

**Lemma 2** (Triangle packing to clique partition). *For every graph $G$, $$\operatorname{cp}(G)\le |E(G)|-2\nu_3(G).$$*

</div>

<div class="proof">

*Proof.* Start with the partition of $E(G)$ into singleton-edge cliques, which has $|E(G)|$ parts. For each triangle in an edge-disjoint triangle packing, replace its three singleton-edge cliques by one triangle clique. This saves two cliques per packed triangle. Applying this to a maximum triangle packing gives the inequality. ◻

</div>

# Imported fractional theorem

The main input from Paper C is the following.

<div id="thm:fractional" class="theorem">

**Theorem 3** (Fractional Chordal Theorem, Paper C). *For every chordal graph $G$ on $n$ vertices, $$|E(G)|-2\nu_3^*(G)
    \le
    \left(\frac16+o(1)\right)n^2.$$*

</div>

Paper C proves this theorem using the clique-tree decomposition and local toolkit developed in Paper B.

# Fractional-to-integral triangle rounding

We use the standard fixed-family fractional-to-integral packing theorem of Haxell–Rödl and Yuster. In the special case needed here, it says the following.

<div id="thm:rounding" class="theorem">

**Theorem 4** (Fractional-to-integral triangle rounding). *For every $n$-vertex graph $G$, $$\nu_3(G)\ge \nu_3^*(G)-o(n^2).$$*

</div>

<div class="remark">

**Remark 5**. The general theorem applies to any fixed finite family of graphs. Here we apply it to the one-element family $\{K_3\}$.

</div>

# Upper bound

Let $G$ be chordal on $n$ vertices. By Lemma <a href="#lem:packing-to-cp" data-reference-type="ref" data-reference="lem:packing-to-cp">2</a>, $$\operatorname{cp}(G)
    \le
    |E(G)|-2\nu_3(G).$$ By Theorem <a href="#thm:rounding" data-reference-type="ref" data-reference="thm:rounding">4</a>, $$\nu_3(G)\ge\nu_3^*(G)-o(n^2),$$ so $$\operatorname{cp}(G)
    \le
    |E(G)|-2\nu_3^*(G)+o(n^2).$$ Using Theorem <a href="#thm:fractional" data-reference-type="ref" data-reference="thm:fractional">3</a>, we get $$\operatorname{cp}(G)
    \le
    \left(\frac16+o(1)\right)n^2.$$

Thus $$\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
    \le
    \left(\frac16+o(1)\right)n^2.$$

# Sharpness

The lower bound is supplied by the split graph construction from Paper A.

<div id="thm:split-lower" class="theorem">

**Theorem 6** (Split lower bound, Paper A). *Let $$G_p=K_p\vee\overline{K}_{2p}.$$ Then $G_p$ is split, hence chordal, has $n=3p$ vertices, and satisfies $$\operatorname{cp}(G_p)\ge \frac{n^2}{6}-O(n).$$*

</div>

Since every split graph is chordal, Theorem <a href="#thm:split-lower" data-reference-type="ref" data-reference="thm:split-lower">6</a> gives $$\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
    \ge
    \frac{n^2}{6}-O(n).$$

Combining the lower bound with the upper bound proves Theorem <a href="#thm:main" data-reference-type="ref" data-reference="thm:main">1</a>.

# Proof-status audit

<div class="center">

| Item                             | Source           | Status                                                 |
|:---------------------------------|:-----------------|:-------------------------------------------------------|
| Split lower bound                | Paper A          | preprint                                               |
| Local chordal toolkit            | Paper B          | preprint; includes local toolkit and certificate usage |
| Fractional chordal theorem       | Paper C          | preprint; imports Paper B                              |
| Fractional-to-integral rounding  | external theorem | standard fixed-family rounding theorem                 |
| Chordal clique partition theorem | Paper D          | preprint; follows from above                           |

</div>

# Discussion

Paper D is intentionally short. The difficult parts of the argument are not in this paper: the split extremal construction is treated in Paper A, and the fractional chordal theorem is proved in Papers B and C. The role of this preprint is to make explicit that the fractional result is strong enough to imply the integral clique partition theorem asymptotically.

A possible final presentation choice is to merge this preprint into the end of Paper C. Keeping Paper D separate has the advantage of cleanly distinguishing the fractional chordal theorem from the final clique partition corollary.

# Further directions

The final theorem leaves several natural follow-up questions.

1.  **Exact finite bounds.** The result is asymptotic. Determining the best possible $O(n)$ term, or exact extremal values for finite $n$, remains open.

2.  **Constructive partitions.** The proof route is through fractional triangle packing and asymptotic rounding. It would be useful to extract explicit near-optimal clique partitions for chordal graphs.

3.  **Shorter proofs for subclasses.** The split case has a much cleaner proof, and intermediate chordal subclasses may admit simpler arguments.

4.  **Presentation choice.** Paper D may ultimately remain standalone or be merged into Paper C as the final rounding section.

# Acknowledgements and use of AI-assisted tools

The author is deeply grateful to his wife María Paz and to his children Lucas, Juan Cristóbal, Francisca, Raimundo, and Benjamín for their love, patience, and support during the development of this work.

The author used AI-assisted tools, including Gemini 3.5 Pro and ChatGPT, during the development of this work for exploratory search, testing possible approaches, looking for contradictions, organizing proof strategies, improving exposition, and preparing drafts. All mathematical claims, proofs, citations, and final editorial decisions are the sole responsibility of the author. No AI system is listed as an author.

<div class="thebibliography">

9

G.-T. Chen, P. Erdős, and E. T. Ordman, *Clique partitions of split graphs*, in *Combinatorics, graph theory, algorithms and applications* (Beijing, 1993), 21–30, 1994.

P. Erdős, E. T. Ordman, and Y. Zalcstein, *Clique partitions of chordal graphs*, Combinatorics, Probability and Computing (1993), 409–415.

P. Erdős, A. W. Goodman, and L. Pósa, *The representation of a graph by set intersections*, Canadian Journal of Mathematics 18 (1966), 106–112.

P. E. Haxell and V. Rödl, *Integer and fractional packings in dense graphs*, Combinatorica 21 (2001), 13–38.

R. Yuster, *Integer and fractional packing of families of graphs*, Combinatorica 28 (2008), 245–251.

</div>
