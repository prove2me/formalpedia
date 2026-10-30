-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:32:18.261885+00:00
-- url     : https://prove2.me/theorems/9c4488d4-e053-4379-8b1c-5bcd6e155075
-- title:
--   A finite planar drawing has a maximal drawable supergraph
-- statement:
--   Every finite graph with a drawing has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs. This includes disconnected starting graphs; the extension must preserve the original vertex set and the given drawing’s planarity predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
