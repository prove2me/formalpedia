-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a2
-- name    : WilliamsonShmoys.planar_edge_count_bound__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:50:24.700239+00:00
-- url     : https://prove2.me/theorems/e0605b2b-a2c2-4550-811f-f61ce2015061
-- title:
--   Simple planar graph edge bound
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges. The bound is tight for a triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_bound__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
