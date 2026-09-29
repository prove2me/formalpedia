-- Prove2me | Definitions.Def_KServer_tree_metric
-- name    : KServer_tree_metric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-31T13:44:03.836712+00:00
-- url     : https://prove2.me/theorems/7a101d66-720d-47c4-96cf-0b483a5c6008
-- title:
--   Tree metric spaces (vertex sets of weighted trees)
-- statement:
--   `IsTreeVertexSpace M` says the metric space $M$ is the vertex set of a weighted tree: there is a tree graph on $M$ (connected and acyclic) and an edge-weight function such that the distance between any two points equals the total weight of the (unique) tree path between them. `walkWeight` sums the weights of the directed edges traversed by a walk. This matches the k-server literature's "let $V$ be the set of vertices of a tree".
-- source:
--   C. Coester, E. Koutsoupias, Towards the k-server conjecture, ICALP 2021, https://arxiv.org/abs/2102.10474, Section 6; M. Chrobak, L. Larmore, An optimal on-line algorithm for k servers on trees, SIAM J. Computing 20(1), 1991

import Mathlib

namespace KServer

/-- The total edge-weight of a walk in a graph: the sum of `w u v` over the
directed edges `(u, v)` traversed by the walk. -/
noncomputable def walkWeight {V : Type*} {G : SimpleGraph V} (w : V → V → ℝ)
    {u v : V} (p : G.Walk u v) : ℝ :=
  (p.darts.map fun d => w d.toProd.1 d.toProd.2).sum

/-- `IsTreeVertexSpace M`: the metric space `M` is (the vertex set of) a
weighted tree — there is a tree graph on `M` and an edge-weight function `w`
such that the distance between any two points equals the total weight of the
(necessarily unique) path between them in the tree. -/
def IsTreeVertexSpace (M : Type*) [MetricSpace M] : Prop :=
  ∃ G : SimpleGraph M, G.IsTree ∧ ∃ w : M → M → ℝ,
    ∀ (u v : M) (p : G.Path u v), dist u v = walkWeight w (p : G.Walk u v)

end KServer


