-- Prove2me | Theorems.Thm_KServer_tree_four_point
-- name    : KServer.tree_four_point
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T19:35:04.979899+00:00
-- url     : https://prove2.me/theorems/1a27516a-0dfb-4e5d-bf8a-e697e2ff75ff
-- title:
--   Tree metrics satisfy the four-point condition
-- statement:
--   A metric space that is the vertex set of a weighted tree satisfies the **four-point condition**: for any four points,
--
--   $$ab + cd \;\le\; \max\{\,ac + bd,\; ad + bc\,\}.$$
--
--   Equivalently, of the three ways of pairing four points, the largest total is attained at least twice.
--
--   ## Role
--
--   This is the property Coester and Koutsoupias call *quasiconcavity* of the metric — the statement that $-d$, viewed as a function on two-point sets, is quasiconvex — and their proof that the Work Function Algorithm is $3$-competitive for three servers on trees rests on it. It is also the classical characterisation of tree metrics: a finite metric satisfies the four-point condition if and only if it is the leaf-distance of some weighted tree. Only the easy direction is asserted here, which is the one the analysis consumes.
--
--   The condition should be read as saying that trees are $0$-hyperbolic. Its role in the $k$-server analysis is that it lets a pair of work-function values be re-matched: where quasiconvexity of the work function offers a choice between two rematchings, quasiconcavity of the *metric* fixes which of the accompanying distance terms is the larger, and the two together pin down the case analysis.
--
--   The proof is the observation that in a tree any three points have a **median** — a point lying metrically between each of the three pairs — and that two points of a geodesic are comparable along it. Given four points $a,b,c,d$, take the medians $m$ of $(a,b,c)$ and $n$ of $(a,b,d)$, both of which lie on the path from $a$ to $b$; whichever of them is nearer to $a$ determines which of the two pairings dominates, and the estimate is then the triangle inequality applied along $c \to m \to n \to d$.
--
--   **Formalization note.** The hypothesis is that the metric space *is* the vertex set of a tree — internal vertices included — and that distances are the total weights of the (unique) connecting paths. Medians are produced by taking, among the vertices lying on both the path from $a$ to $b$ and the path from $a$ to $c$, one farthest from $a$; that this is a median follows because the two path-tails beyond it are disjoint, so their concatenation is again a path and hence, by uniqueness of paths in a tree, is the path from $b$ to $c$.
-- source:
--   C. Coester, E. Koutsoupias, Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle, ICALP 2021, arXiv:2102.10474, Section 6 and Appendix (Quasiconcavity and trees): 'a metric (M,d) is a tree if and only if the map d is quasiconcave (i.e., -d is quasiconvex when viewed as a function defined on 2-point sets). Our proof that WFA is 3-competitive for the 3-server problem on trees crucially relies on this property.' Only the direction from trees to quasiconcavity is stated here.

import Mathlib
import Definitions.Def_KServer_tree_metric

namespace KServer

theorem tree_four_point (M : Type) [MetricSpace M] [Fintype M] (hM : IsTreeVertexSpace M)
    (a b c d : M) :
    dist a b + dist c d ≤ max (dist a c + dist b d) (dist a d + dist b c) := by sorry

end KServer
