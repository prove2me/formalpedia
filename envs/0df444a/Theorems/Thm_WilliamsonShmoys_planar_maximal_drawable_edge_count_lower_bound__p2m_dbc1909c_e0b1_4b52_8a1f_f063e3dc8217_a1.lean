-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_drawable_edge_count_lower_bound__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1
-- name    : WilliamsonShmoys.planar_maximal_drawable_edge_count_lower_bound__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:49:44.448567+00:00
-- url     : https://prove2.me/theorems/dd6ad35b-d06d-4359-826f-34a5efd43246
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable graphs on the same vertex set has at least 3|V|−6 edges. The intended independent route is to show every face in a maximal planar embedding is triangular, combine the face-edge incidence count with Euler's formula, and conclude the exact edge count 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_drawable_edge_count_lower_bound__p2m_dbc1909c_e0b1_4b52_8a1f_f063e3dc8217_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hMax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K = H) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
