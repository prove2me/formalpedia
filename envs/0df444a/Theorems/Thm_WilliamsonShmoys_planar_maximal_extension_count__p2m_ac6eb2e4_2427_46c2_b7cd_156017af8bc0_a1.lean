-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_count__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1
-- name    : WilliamsonShmoys.planar_maximal_extension_count__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:48.29622+00:00
-- url     : https://prove2.me/theorems/45bc859f-c802-4c58-986e-c045911051ac
-- title:
--   Drawable triangulated extension count
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension_count__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : ∃ J : SimpleGraph V, G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧ J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
