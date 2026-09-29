-- Prove2me | solution 1 for BanditAlgorithm.measurable_gittinsFiniteRetirementValue
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:12:32.628699+00:00
-- url     : https://prove2.me/submissions/209143ae-440f-4af0-a87c-64cfda21588a

import Definitions.Def_GittinsFiniteRetirementValue

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) :
    ∀ n, Measurable (gittinsFiniteRetirementValue P r α γ n) := by
  intro n
  induction n with
  | zero =>
      simp [gittinsFiniteRetirementValue]
  | succ n ih =>
      have hint : Measurable (fun x ↦
          ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x) :=
        ih.stronglyMeasurable.integral_kernel.measurable
      rw [show gittinsFiniteRetirementValue P r α γ (n + 1) =
          fun x ↦ max 0 (r x - γ +
            α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x) by rfl]
      exact measurable_const.max
        ((hr.sub measurable_const).add (measurable_const.mul hint))
