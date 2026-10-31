-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:54:53.280767+00:00
-- url     : https://prove2.me/theorems/b1eaa68f-d3bc-482e-8876-be28beef9c21
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every finite drawable graph has an inclusion-maximal drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ T : SimpleGraph V, G ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T := by sorry
