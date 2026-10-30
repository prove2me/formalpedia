-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_planar_upper_bound
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_planar_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:19:20.591419+00:00
-- url     : https://prove2.me/theorems/ab2b8b90-1738-4482-b155-453e4a924c67
-- title:
--   Euler edge bound for a drawable simple graph
-- statement:
--   Every drawable simple graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_planar_upper_bound {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hTdraw : WilliamsonShmoys.HasPlanarDrawingOn T) (hCard : 3 ≤ Fintype.card V) : T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
