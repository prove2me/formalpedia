-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_of_disconnected
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_of_disconnected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:58:42.105912+00:00
-- url     : https://prove2.me/theorems/1a05302a-75ce-4e0f-8bf2-e3af4cd61945
-- title:
--   Augmenting a disconnected planar drawing
-- statement:
--   Any disconnected graph with a crossing-free drawing on at least three vertices has a planar supergraph on the same vertices with strictly more edges. This packages the geometric augmentation needed by the parent; the parent then contradicts edge-count maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_count_of_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ ∀ u v, Relation.ReflTransGen H.Adj u v) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard < K.edgeSet.ncard := by sorry
