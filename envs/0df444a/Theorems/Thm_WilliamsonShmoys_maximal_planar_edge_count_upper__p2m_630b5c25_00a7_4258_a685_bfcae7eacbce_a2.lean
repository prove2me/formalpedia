-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:54.691972+00:00
-- url     : https://prove2.me/theorems/df7a90bf-1bc9-431d-9ba0-e2c2ea0f37ff
-- title:
--   Euler upper bound for a finite planar drawing
-- statement:
--   A finite graph with the supplied crossing-free drawing and at least three vertices has at most 3V − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_630b5c25_00a7_4258_a685_bfcae7eacbce_a2 {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
