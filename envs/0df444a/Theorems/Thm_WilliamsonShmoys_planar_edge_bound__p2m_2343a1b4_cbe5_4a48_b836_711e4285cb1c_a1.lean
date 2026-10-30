-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:24:39.66829+00:00
-- url     : https://prove2.me/theorems/1e99581f-fcbc-4e9a-9e15-d8d615ea77d1
-- title:
--   Simple planar edge bound
-- statement:
--   A finite simple graph with the specified planar drawing and at least three vertices has at most three times its vertex count minus six edges, stated without natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
