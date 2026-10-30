-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2
-- name    : WilliamsonShmoys_planar_edge_upper_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:30:00.554016+00:00
-- url     : https://prove2.me/theorems/e69ed9eb-68bb-4280-ac9e-246f714b2ccd
-- title:
--   Simple planar graphs have at most three times the vertices minus six edges
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3V−6 edges. This is the topological graph bound needed to prove the target’s second inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys_planar_edge_upper_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
