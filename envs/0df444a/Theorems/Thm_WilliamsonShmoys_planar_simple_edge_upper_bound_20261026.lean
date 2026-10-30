-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper_bound_20261026
-- name    : WilliamsonShmoys.planar_simple_edge_upper_bound_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:21:53.257663+00:00
-- url     : https://prove2.me/theorems/c6520550-baff-47ed-82af-eac6a721136f
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A simple graph with the supplied crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_upper_bound_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
