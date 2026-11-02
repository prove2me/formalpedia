-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_extension__p2m_0df19a3a_91dd_4e4b_942c_e5b79d23d807_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_0df19a3a_91dd_4e4b_942c_e5b79d23d807_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:41:22.825037+00:00
-- url     : https://prove2.me/theorems/8e688b5a-4cd6-4a71-af1c-8dd5b2ac94c3
-- title:
--   Planar graph extends to a triangulation on the same vertices
-- statement:
--   Every finite simply planar graph with at least three vertices is a subgraph of a triangulated planar graph on the same vertex set, with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_triangulation_extension__p2m_0df19a3a_91dd_4e4b_942c_e5b79d23d807_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G.edgeFinset ⊆ K.edgeFinset ∧
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
