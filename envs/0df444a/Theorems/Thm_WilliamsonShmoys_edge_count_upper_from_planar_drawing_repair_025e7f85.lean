-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_upper_from_planar_drawing_repair_025e7f85
-- name    : WilliamsonShmoys.edge_count_upper_from_planar_drawing_repair_025e7f85
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:27:19.65863+00:00
-- url     : https://prove2.me/theorems/9f9f6fc9-eb57-444d-aa6f-ef32e3cb596b
-- title:
--   Euler edge bound from a planar drawing
-- statement:
--   A finite simple graph with the specified planar drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_upper_from_planar_drawing_repair_025e7f85 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
