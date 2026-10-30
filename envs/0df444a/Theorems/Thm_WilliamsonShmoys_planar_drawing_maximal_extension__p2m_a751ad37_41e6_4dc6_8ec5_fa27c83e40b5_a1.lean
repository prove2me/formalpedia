-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:47:32.624775+00:00
-- url     : https://prove2.me/theorems/9ccc17e7-d57a-4505-aa89-bf47948d85c9
-- title:
--   Every finite drawable graph has a maximal drawable supergraph
-- statement:
--   A drawable graph on a finite vertex type has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      ∀ K : SimpleGraph V,
        G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ G := by sorry
