-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite_choice
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_finite_choice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:40:35.108352+00:00
-- url     : https://prove2.me/theorems/323bc778-3cfb-4700-a3f3-234ba87e87d6
-- title:
--   A finite drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_finite_choice
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V,
        S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S := by sorry
