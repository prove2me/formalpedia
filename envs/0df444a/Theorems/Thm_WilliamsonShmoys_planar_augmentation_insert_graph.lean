-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_insert_graph
-- name    : WilliamsonShmoys.planar_augmentation_insert_graph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:46:22.655726+00:00
-- url     : https://prove2.me/theorems/fcf4625f-72cf-476d-9bb8-082ff8aaa968
-- title:
--   Bookkeeping for inserting the connector edge
-- statement:
--   For the graph formed by inserting `{u,v}` into the edge set, prove that old adjacencies remain, that the new edge was absent before and the resulting edge set is exactly the insertion, and that `u` and `v` are adjacent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_augmentation_insert_graph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (u v : V)
    (hdisconnected : ¬ Relation.ReflTransGen H.Adj u v) :
    let K : SimpleGraph V :=
      SimpleGraph.fromEdgeSet (insert s(u, v) H.edgeSet)
    (∀ {x y : V}, H.Adj x y → K.Adj x y) ∧
      (∃ e : Sym2 V, e ∉ H.edgeSet ∧ K.edgeSet = insert e H.edgeSet) ∧
      K.Adj u v := by
  sorry
