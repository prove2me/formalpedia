-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_completion__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_completion__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:26:03.494955+00:00
-- url     : https://prove2.me/theorems/af53018e-a3f0-4da9-93f9-d5c32320c2f0
-- title:
--   Maximal drawable completion on the same vertices
-- statement:
--   Extend the given drawable graph to an inclusion-maximal drawable graph on the same finite vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_completion__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet = H.edgeSet) := by sorry
