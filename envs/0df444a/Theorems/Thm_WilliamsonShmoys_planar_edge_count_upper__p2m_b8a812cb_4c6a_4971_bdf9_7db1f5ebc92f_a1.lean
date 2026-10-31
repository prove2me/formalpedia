-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_b8a812cb_4c6a_4971_bdf9_7db1f5ebc92f_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_b8a812cb_4c6a_4971_bdf9_7db1f5ebc92f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:59:21.300997+00:00
-- url     : https://prove2.me/theorems/5a9827f9-82f3-4b58-ad88-46e664a4abfc
-- title:
--   Planar simple graphs satisfy the edge upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_b8a812cb_4c6a_4971_bdf9_7db1f5ebc92f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
