-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_pair_augmentation
-- name    : WilliamsonShmoys.planar_disconnected_pair_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:16:57.205102+00:00
-- url     : https://prove2.me/theorems/f5ebefdf-c5c3-4633-ab4b-6fe7351cd86c
-- title:
--   Add an edge between specified disconnected vertices
-- statement:
--   Given a planar drawing and two vertices in different connected components, add exactly one new edge so that it joins those vertices, preserves all old adjacencies, and the resulting graph still has a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_pair_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (u v : V)
    (hdisconnected : ¬ Relation.ReflTransGen H.Adj u v) :
    ∃ K : SimpleGraph V,
      (∀ ⦃x y⦄, H.Adj x y → K.Adj x y) ∧
      (∃ e : Sym2 V, e ∉ H.edgeSet ∧ K.edgeSet = insert e H.edgeSet) ∧
      K.Adj u v ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by
  sorry
