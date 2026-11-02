-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_55bcde83_43a5_4c62_ba9b_1744a34b8f86_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_55bcde83_43a5_4c62_ba9b_1744a34b8f86_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:05:10.305388+00:00
-- url     : https://prove2.me/theorems/9c97ddbc-3433-4f41-a8eb-d0def08933ca
-- title:
--   Triangulation extension of a planar drawing
-- statement:
--   A crossing-free drawing of a finite simple graph with at least three vertices can be completed, on the same vertex set, to a simple graph whose edge set contains the original edges and whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_55bcde83_43a5_4c62_ba9b_1744a34b8f86_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V),
      (∀ [DecidableRel H.Adj],
        G.edgeFinset ⊆ H.edgeFinset ∧
        H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  sorry
