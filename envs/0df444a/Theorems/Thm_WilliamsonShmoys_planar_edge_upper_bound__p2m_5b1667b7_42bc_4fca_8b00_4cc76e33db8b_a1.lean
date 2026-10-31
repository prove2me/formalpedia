-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:27:51.035778+00:00
-- url     : https://prove2.me/theorems/2cc4f687-238d-40a3-a706-2eb34249ae45
-- title:
--   Planar simple graphs have at most 3n−6 edges
-- statement:
--   Every finite simple graph with at least three vertices that has a drawing as defined in the supplied module has at most 3|V|−6 edges. The vertex-count hypothesis preserves the range where this bound is valid.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
