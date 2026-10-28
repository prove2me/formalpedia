-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_augmentation_6c0819c8_795c_411a_aacd_f8cf4c691759
-- name    : WilliamsonShmoys.maximal_planar_edge_count_augmentation_6c0819c8_795c_411a_aacd_f8cf4c691759
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:00:18.562087+00:00
-- url     : https://prove2.me/theorems/31b015c9-af2a-4de7-a72a-7341ac47b499
-- title:
--   Planar augmentation edge lower bound
-- statement:
--   Extend any planar simple graph on at least three vertices to a planar supergraph on the same vertex set with at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_augmentation_6c0819c8_795c_411a_aacd_f8cf4c691759
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V,
      HasPlanarDrawingOn U ∧
      (∀ u v, T.Adj u v → U.Adj u v) ∧
      3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by sorry
