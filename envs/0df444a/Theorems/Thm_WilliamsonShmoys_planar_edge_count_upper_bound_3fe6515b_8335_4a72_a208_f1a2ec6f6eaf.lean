-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_3fe6515b_8335_4a72_a208_f1a2ec6f6eaf
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_3fe6515b_8335_4a72_a208_f1a2ec6f6eaf
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:37:24.098922+00:00
-- url     : https://prove2.me/theorems/a0b92b21-6aa1-495e-a7c5-b4d4c91a44bd
-- title:
--   Planar graph edge upper bound for the maximal planar count target
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most `3n − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_3fe6515b_8335_4a72_a208_f1a2ec6f6eaf {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
