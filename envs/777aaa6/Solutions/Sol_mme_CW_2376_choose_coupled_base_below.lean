-- Prove2me | solution 1 for mme_CW_2376_choose_coupled_base_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:30:04.323257+00:00
-- url     : https://prove2.me/submissions/f93c8054-b378-4ad4-8327-620b83ff40b0

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_mme_CW_auxiliary_RHS_coupled

open MME Filter

/-!
Choosing one attained coupled base close enough to the raw boundary.

The generalized auxiliary expression is continuous in its positive coupled
base.  Approaching the raw base from below therefore preserves any fixed
strict lower target for all sufficiently late terms.
-/

theorem solution
    (tau V : ℝ)
    (hV_lt :
      V < auxiliaryRHS 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d) :
    ∃ Vc : ℝ,
      0 ≤ Vc ∧
      Vc <
        4 * (6 : ℝ) ^ (3 * tau) *
          ((6 : ℝ) ^ (3 * tau) + 2) ∧
      V < auxiliaryRHSWithCoupled 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d Vc := by
  let C : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) *
      ((6 : ℝ) ^ (3 * tau) + 2)
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  let VcSeq : ℕ → ℝ := fun n =>
    C - (((n + 1 : ℕ) : ℝ))⁻¹
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hinv :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹)
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hshift
  have hVcSeq : Tendsto VcSeq atTop (nhds C) := by
    have hconst :
        Tendsto (fun _ : ℕ => C) atTop (nhds C) :=
      tendsto_const_nhds
    simpa [VcSeq] using hconst.sub hinv
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hcont :
      ContinuousAt
        (fun x : ℝ =>
          auxiliaryRHSWithCoupled 6 tau
            cw2376_a cw2376_b cw2376_c cw2376_d x) C := by
    unfold auxiliaryRHSWithCoupled
    exact
      ((continuousAt_const.mul continuousAt_const).mul
        (Real.continuousAt_rpow_const C cw2376_d (Or.inl hC_ne))).div_const _
  have haux_tend :
      Tendsto
        (fun n : ℕ =>
          auxiliaryRHSWithCoupled 6 tau
            cw2376_a cw2376_b cw2376_c cw2376_d (VcSeq n))
        atTop
        (nhds
          (auxiliaryRHS 6 tau
            cw2376_a cw2376_b cw2376_c cw2376_d)) := by
    have hraw := hcont.tendsto.comp hVcSeq
    simpa [C, auxiliaryRHSWithCoupled, auxiliaryRHS] using hraw
  have hVc_pos : ∀ᶠ n : ℕ in atTop, 0 < VcSeq n :=
    (tendsto_order.1 hVcSeq).1 0 hC_pos
  have hV_aux : ∀ᶠ n : ℕ in atTop,
      V < auxiliaryRHSWithCoupled 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d (VcSeq n) :=
    (tendsto_order.1 haux_tend).1 V hV_lt
  obtain ⟨n, hnpos, hnaux⟩ := (hVc_pos.and hV_aux).exists
  refine ⟨VcSeq n, hnpos.le, ?_, hnaux⟩
  dsimp [VcSeq]
  exact sub_lt_self C (by positivity)
