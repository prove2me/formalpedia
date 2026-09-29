-- Prove2me | solution 1 for VectorSpaceOpt.hahn_banach_norm_preserving
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:47:48.409413+00:00
-- url     : https://prove2.me/submissions/3c0681fb-27db-4712-aff4-8c47585b59ca

import Mathlib


theorem solution {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (M : Submodule ℝ X) (f : M →L[ℝ] ℝ) :
    ∃ F : X →L[ℝ] ℝ, (∀ m : M, F m = f m) ∧ ‖F‖ = ‖f‖ := by
  exact Real.exists_extension_norm_eq M f
