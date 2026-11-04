-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_e26f4eeb_ea90_4bc7_9f3f_02f85b28272b_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_e26f4eeb_ea90_4bc7_9f3f_02f85b28272b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:44:57.858836+00:00
-- url     : https://prove2.me/theorems/8963bb62-e14c-4266-badc-3102e502f664
-- title:
--   Triangulation completion of a planar drawing
-- statement:
--   Any finite simple graph with at least three vertices and a crossing-free drawing is contained in a triangulated planar simple graph on the same vertex set, whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_e26f4eeb_ea90_4bc7_9f3f_02f85b28272b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      HasPlanarDrawingOn H ∧
      (∀ u v, K.Adj u v → H.Adj u v) ∧
      K.edgeFinset.card ≤ (by letI : DecidableRel H.Adj := dH; exact H.edgeFinset.card) ∧
      (by letI : DecidableRel H.Adj := dH; exact H.edgeFinset.card) = 3 * Fintype.card V - 6 := by sorry
