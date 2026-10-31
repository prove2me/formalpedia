-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:53:23.768581+00:00
-- url     : https://prove2.me/theorems/07b3b32c-255b-4e37-9ffb-d7128bfa6740
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Any simple graph with a crossing-free drawing on at least three finite vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
