-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:42:46.350986+00:00
-- url     : https://prove2.me/theorems/35749f10-3b92-4bc3-9d25-6f769792d1fb
-- title:
--   Edge upper bound for a planar drawing
-- statement:
--   Any finite simple graph with at least three vertices and the supplied crossing-free drawing has at most 3n − 6 edges. This is the Euler-formula upper bound; its proof must also cover disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Tactic
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_fa30b313_3ade_47b7_9dcc_bae00c9eb7a0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
