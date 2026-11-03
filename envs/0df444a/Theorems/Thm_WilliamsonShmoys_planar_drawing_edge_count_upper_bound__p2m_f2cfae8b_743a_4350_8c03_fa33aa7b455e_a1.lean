-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:11.846548+00:00
-- url     : https://prove2.me/theorems/cd9164cf-4b74-4ea8-8748-881de168cba7
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every drawable simple graph with at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hcard : 3 <= Fintype.card V) : (letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card <= 3 * Fintype.card V - 6) := by sorry
