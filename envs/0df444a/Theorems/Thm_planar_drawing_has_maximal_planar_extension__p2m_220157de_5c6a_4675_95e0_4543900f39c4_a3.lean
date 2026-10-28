-- Prove2me | Theorems.Thm_planar_drawing_has_maximal_planar_extension__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
-- name    : planar_drawing_has_maximal_planar_extension__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:23:39.73162+00:00
-- url     : https://prove2.me/theorems/8523885d-5a38-4a4c-a926-9e6dc9f2f875
-- title:
--   Extend a finite planar drawing to a maximal planar supergraph
-- statement:
--   Every finite graph with the supplied drawing has a drawing-preserving supergraph on the same vertex type that is maximal among graphs with such drawings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem planar_drawing_has_maximal_planar_extension__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
