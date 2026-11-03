-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_card_upper_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- name    : WilliamsonShmoys.planar_edge_card_upper_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:42:45.151388+00:00
-- url     : https://prove2.me/theorems/ef56db37-3285-4935-af76-5046b2776a5c
-- title:
--   Euler’s upper edge bound for a drawable graph
-- statement:
--   A simple graph with a crossing-free drawing on at least three finite ordered vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_card_upper_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) [DecidableRel K.Adj] (hcard : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
