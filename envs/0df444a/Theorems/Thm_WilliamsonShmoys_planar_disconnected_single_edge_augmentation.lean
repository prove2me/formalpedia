-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_single_edge_augmentation
-- name    : WilliamsonShmoys.planar_disconnected_single_edge_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:02:39.831489+00:00
-- url     : https://prove2.me/theorems/4a44723c-a060-47df-b865-8281690ce3f8
-- title:
--   Add one edge between disconnected planar components
-- statement:
--   For a disconnected graph with a crossing-free drawing, augment it by exactly one new edge while keeping all old adjacencies and a crossing-free drawing on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_single_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ ∀ u v, Relation.ReflTransGen H.Adj u v) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      (∃ e : Sym2 V, e ∉ H.edgeSet ∧ K.edgeSet = insert e H.edgeSet) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by
  sorry
