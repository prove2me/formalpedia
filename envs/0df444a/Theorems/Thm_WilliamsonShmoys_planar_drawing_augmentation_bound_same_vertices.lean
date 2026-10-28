-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_bound_same_vertices
-- name    : WilliamsonShmoys.planar_drawing_augmentation_bound_same_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:39:27.801624+00:00
-- url     : https://prove2.me/theorems/23f6598a-3170-4674-aead-aee7adf41df1
-- title:
--   Planar drawing completion edge bound on the same vertices
-- statement:
--   Any graph on a finite linearly ordered vertex type with at least three vertices that has a crossing-free drawing can be extended to a planar supergraph on that same vertex type with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation_bound_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧ G ≤ K ∧
      3 * (Fintype.card V : Int) - 6 <= (K.edgeSet.ncard : Int) := by
  sorry
