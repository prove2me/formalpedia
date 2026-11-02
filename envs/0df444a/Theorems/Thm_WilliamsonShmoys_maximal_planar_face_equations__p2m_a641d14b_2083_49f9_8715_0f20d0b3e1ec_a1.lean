-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations__p2m_a641d14b_2083_49f9_8715_0f20d0b3e1ec_a1
-- name    : WilliamsonShmoys.maximal_planar_face_equations__p2m_a641d14b_2083_49f9_8715_0f20d0b3e1ec_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:46:19.297061+00:00
-- url     : https://prove2.me/theorems/addb50df-8cce-4ac7-84ef-2e1f35b931aa
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For a maximal drawable simple graph on at least three vertices, there is a face count satisfying Euler’s equation and the triangular face-edge incidence equation. The first equation counts vertices, faces, and edges; the second expresses that every face has three boundary edges and every edge is incident to two faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_face_equations__p2m_a641d14b_2083_49f9_8715_0f20d0b3e1ec_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → H ≤ L → L = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
        3 * f = 2 * H.edgeFinset.card) := by sorry
