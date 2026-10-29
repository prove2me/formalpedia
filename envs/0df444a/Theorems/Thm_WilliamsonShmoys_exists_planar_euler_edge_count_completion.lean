-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_euler_edge_count_completion
-- name    : WilliamsonShmoys.exists_planar_euler_edge_count_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:04:37.198212+00:00
-- url     : https://prove2.me/theorems/8eefa310-d5a0-4ce6-aaa5-8cc496cd2f86
-- title:
--   Planar completion with Euler edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices has a planar supergraph on the same vertex type whose edge count is 3 times the number of vertices minus 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_euler_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
