-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:55:43.384843+00:00
-- url     : https://prove2.me/theorems/1385cb7a-0cd6-4a77-af6d-ce9c0f4254da
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable graph on the given finite vertex set has a drawable supergraph that is maximal among drawable supergraphs on that same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a546b4df_cdfe_4033_ada4_bee990d9e0a1_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 <= Fintype.card V) : ∃ S : SimpleGraph V, R ≤ S ∧ HasPlanarDrawingOn S ∧ ∀ T : SimpleGraph V, S ≤ T → HasPlanarDrawingOn T → T = S := by sorry
