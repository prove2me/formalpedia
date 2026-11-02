-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion__p2m_dbc103f7_2bde_446c_9b3b_46d38358163c_a1
-- name    : WilliamsonShmoys.planar_drawing_completion__p2m_dbc103f7_2bde_446c_9b3b_46d38358163c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:55:14.11553+00:00
-- url     : https://prove2.me/theorems/28ba4808-169d-4087-9472-de8f0bf86338
-- title:
--   Completion of a drawable graph to a triangulation
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the number of vertices minus six. The completion also preserves the corresponding edge-count inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_completion__p2m_dbc103f7_2bde_446c_9b3b_46d38358163c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ K : SimpleGraph V,
      letI : DecidableRel K.Adj := Classical.decRel K.Adj
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeFinset.card ≤ K.edgeFinset.card ∧
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
