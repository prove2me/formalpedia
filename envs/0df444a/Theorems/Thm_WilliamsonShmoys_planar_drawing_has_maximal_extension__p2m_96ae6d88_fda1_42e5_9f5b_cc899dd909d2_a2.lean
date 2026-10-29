-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T21:44:10.539649+00:00
-- url     : https://prove2.me/theorems/48c6a2cb-cbac-47a2-be78-648baaeb349a
-- title:
--   A drawable finite graph has a maximal drawable extension
-- statement:
--   Every drawable finite graph is contained in a drawable graph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
