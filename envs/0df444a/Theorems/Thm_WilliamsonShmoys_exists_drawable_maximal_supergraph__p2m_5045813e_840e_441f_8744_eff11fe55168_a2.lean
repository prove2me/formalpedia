-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_maximal_supergraph__p2m_5045813e_840e_441f_8744_eff11fe55168_a2
-- name    : WilliamsonShmoys.exists_drawable_maximal_supergraph__p2m_5045813e_840e_441f_8744_eff11fe55168_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:02.782239+00:00
-- url     : https://prove2.me/theorems/ffa4438e-4fb3-4daa-bf09-f110a1418dd6
-- title:
--   A drawable graph has a maximal drawable spanning supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices that is maximal under inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_drawable_maximal_supergraph__p2m_5045813e_840e_441f_8744_eff11fe55168_a2 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
