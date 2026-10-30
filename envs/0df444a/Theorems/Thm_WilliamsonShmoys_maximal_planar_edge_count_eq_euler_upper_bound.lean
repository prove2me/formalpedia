-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_euler_upper_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_count_eq_euler_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:47:39.639491+00:00
-- url     : https://prove2.me/theorems/d9e6fa81-f701-488e-92d0-a87ec6c3ec1a
-- title:
--   Planar edge upper bound for maximal edge-count theorem
-- statement:
--   A finite graph with the specified planar drawing and at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_eq_euler_upper_bound {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
