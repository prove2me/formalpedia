-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_across_components__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1
-- name    : WilliamsonShmoys.planar_augmentation_across_components__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:13:54.001455+00:00
-- url     : https://prove2.me/theorems/39e1387e-c6b4-4e32-ad1b-235228b03693
-- title:
--   Planar drawing admits an edge between distinct components
-- statement:
--   If two distinct vertices lie in different components of a graph with a crossing-free drawing, there is a strictly larger planar graph on the same vertices that contains the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_across_components__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1 {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) {u v : V}
    (huv : u ≠ v) (hnotReachable : ¬ H.Reachable u v) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧ ¬ J ≤ H := by sorry
