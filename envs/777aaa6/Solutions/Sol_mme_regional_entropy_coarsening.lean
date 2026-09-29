-- Prove2me | solution 1 for mme_regional_entropy_coarsening
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:52:10.987002+00:00
-- url     : https://prove2.me/submissions/bcf7a8bd-a97b-4ede-aa08-59c10cbcef2f

import Theorems.Thm_mme_regional_mass_entropy_nonnegative
import Mathlib
open BigOperators MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem solution {A J : Type*} [Fintype A] [Fintype J] (g : A → J)
    (x : A → ℝ) (hx : ∀ a, 0 ≤ x a) :
    massEntropy (fun j ↦ ∑ a : {a // g a = j}, x a.val) ≤ massEntropy x := by
  classical
  have hcond : 0 ≤ ∑ j, massEntropy (fun a : {a // g a = j} ↦ x a.val) :=
    Finset.sum_nonneg (fun j _ ↦ mme_regional_mass_entropy_nonnegative _ (fun a ↦ hx a.val))
  have hsum := Fintype.sum_fiberwise g x
  have hent := Fintype.sum_fiberwise g (fun a ↦ Real.negMulLog (x a))
  simp only [massEntropy,entropy,Finset.sum_sub_distrib] at hcond ⊢
  rw [hent] at hcond
  rw [hsum]
  linarith
