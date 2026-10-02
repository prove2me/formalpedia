-- Prove2me | solution 1 for BookSixth.standard_family_isometry_preserves_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T08:40:10.633286+00:00
-- url     : https://prove2.me/submissions/50dce5be-5615-4508-ade2-f3950b7c4ca0

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_standard_circle_is_round
import Theorems.Thm_BookSixth_euclidean_isometry_preserves_roundness

noncomputable section

open scoped BigOperators
open scoped Matrix
open BookSixth
open Matrix

theorem solution (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ x y : Fin 3 → ℝ, (∑ i, (A *ᵥ x) i * (A *ᵥ y) i) = ∑ i, x i * y i)
    (a : ℝ) (ha : 0 < a) (b : Fin 3 → ℝ) (t : ℝ) (i j : ℕ) (hij : i ≠ j) :
    RoundCircle ((fun x : Space3 => (a • (A *ᵥ x)) + b) '' (standardCircle i)) := by
  have hCLM : ∀ x y : Space3,
      (∑ k, (LinearMap.toContinuousLinearMap A.mulVecLin x) k *
        (LinearMap.toContinuousLinearMap A.mulVecLin y) k) = ∑ k, x k * y k := by
    intro x y
    simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply] using hA x y
  have h := BookSixth.euclidean_isometry_preserves_roundness
    (C := standardCircle i) (A := LinearMap.toContinuousLinearMap A.mulVecLin)
    (b := b) (a := a) (hA := hCLM) (ha := ha)
    (hC := BookSixth.standard_circle_is_round i)
  have heq : (fun x : Space3 => a • (A *ᵥ x) + b) '' standardCircle i =
      (fun x : Space3 => a • (LinearMap.toContinuousLinearMap A.mulVecLin) x + b) '' standardCircle i :=
    Set.image_congr fun x _ => by
      simp only [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply]
  simpa only [heq] using h
