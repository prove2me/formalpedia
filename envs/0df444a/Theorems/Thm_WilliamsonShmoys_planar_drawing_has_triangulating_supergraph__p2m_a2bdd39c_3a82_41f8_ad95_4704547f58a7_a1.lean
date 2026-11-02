-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulating_supergraph__p2m_a2bdd39c_3a82_41f8_ad95_4704547f58a7_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulating_supergraph__p2m_a2bdd39c_3a82_41f8_ad95_4704547f58a7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:41:52.558889+00:00
-- url     : https://prove2.me/theorems/6f695848-ebe7-49d1-9027-cfad81c2f288
-- title:
--   Planar drawing extends to a triangulated supergraph
-- statement:
--   Any finite graph with a crossing-free drawing and at least three vertices has a crossing-free planar supergraph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulating_supergraph__p2m_a2bdd39c_3a82_41f8_ad95_4704547f58a7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V, N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (letI : DecidableRel P.Adj := Classical.decRel P.Adj
       3 * Fintype.card V = P.edgeFinset.card + 6) := by sorry
