-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_upper_bound
-- name    : WilliamsonShmoys.planar_drawable_edge_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:50:18.219894+00:00
-- url     : https://prove2.me/theorems/a018efc2-cff0-44c3-8b87-21061ba8b106
-- title:
--   Planar edge upper bound
-- statement:
--   A drawable simple graph with at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_edge_upper_bound {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
