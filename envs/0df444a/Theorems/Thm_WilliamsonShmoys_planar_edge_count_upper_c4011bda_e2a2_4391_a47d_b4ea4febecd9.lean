-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- name    : WilliamsonShmoys.planar_edge_count_upper_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:13:15.669676+00:00
-- url     : https://prove2.me/theorems/7369ad83-f588-4079-99f9-8944a3b3ecab
-- title:
--   Simple planar graphs have at most 3n − 6 edges
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges. The bound follows from Euler’s formula and counting face-edge incidences; the argument must account for disconnected graphs as well.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_c4011bda_e2a2_4391_a47d_b4ea4febecd9
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
