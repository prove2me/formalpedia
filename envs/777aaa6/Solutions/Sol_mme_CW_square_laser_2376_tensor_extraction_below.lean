-- Prove2me | solution 1 for mme_CW_square_laser_2376_tensor_extraction_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:42:01.118088+00:00
-- url     : https://prove2.me/submissions/9b20c280-03ca-49b3-8deb-6d64dd431c4a

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Theorems.Thm_mme_CW_2376_amplified_error_absorbed
import Theorems.Thm_mme_CW_2376_integer_profile
import Theorems.Thm_mme_CW_square_laser_2376_profile_rate_extraction
import Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions

open MME BigOperators Filter

universe u

/-!
Reduction of the tensor-only below-base theorem to the source-faithful
per-root laser extraction.  The fixed 616627-fold coupled-witness error and
the subexponential profile loss are combined into one vanishing loss in the
base, so every strict target below the generalized auxiliary expression is
eventually attained.
-/

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (Vc : ℝ) (hVc_nonneg : 0 ≤ Vc)
    (hVc_value :
      HasTauValueAtLeast
        (cyclicSymmetrization (coupledObj K 6)) tau Vc)
    (V : ℝ) (hV_nonneg : 0 ≤ V)
    (hV_lt :
      V < auxiliaryRHSWithCoupled 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d Vc) :
    ∃ m : ℕ → ℕ,
      Tendsto m atTop atTop ∧
      ∀ᶠ n : ℕ in atTop,
        (3 * (699 * m n) + 6 * (37518 * m n) +
            3 * (307638 * m n) + 3 * (616627 * m n) =
              3000000 * m n ∧
          2 * (699 * m n) + 2 * (37518 * m n) +
              307638 * m n = 384072 * m n ∧
          2 * (37518 * m n) + 2 * (616627 * m n) =
              1308290 * m n ∧
          2 * (307638 * m n) + 616627 * m n =
              1231903 * m n ∧
          2 * (37518 * m n) = 75036 * m n ∧
          699 * m n = 699 * m n ∧
          384072 * m n + 1308290 * m n + 1231903 * m n +
              75036 * m n + 699 * m n = 3000000 * m n) ∧
        ∃ (k : ℕ) (x y z : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
            ((CWObj K 6).kronPow (6000000 * m n)) ∧
          V ^ (3000000 * m n) ≤
            ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  obtain ⟨m, delta, hm, hdelta, hdelta_pos, hwitness⟩ :=
    mme_HasTauValueAtLeast_to_cofinal_finite_extractions
      (cyclicSymmetrization (coupledObj K 6)) tau Vc hVc_value
  obtain ⟨rate, hrate, _hrate_nonneg, hrate_extract⟩ :=
    mme_CW_square_laser_2376_profile_rate_extraction
      (K := K) tau htau Vc hVc_nonneg
  let B : ℝ := auxiliaryRHSWithCoupled 6 tau
    cw2376_a cw2376_b cw2376_c cw2376_d Vc
  have hB_pos : 0 < B := by
    exact lt_of_le_of_lt hV_nonneg hV_lt
  have hden :
      Tendsto (fun n : ℕ => 1 - delta n) atTop (nhds (1 - 0)) := by
    exact tendsto_const_nhds.sub hdelta
  have hfrac :
      Tendsto (fun n : ℕ => delta n / (1 - delta n))
        atTop (nhds 0) := by
    have h := hdelta.div hden (by norm_num : (1 - (0 : ℝ)) ≠ 0)
    simpa using h
  have hloss :
      Tendsto
        (fun n : ℕ =>
          rate (m n) + delta n / (1 - delta n))
        atTop (nhds 0) := by
    simpa using (hrate.comp hm).add hfrac
  have hneg_loss :
      Tendsto
        (fun n : ℕ =>
          -(rate (m n) + delta n / (1 - delta n)))
        atTop (nhds 0) := by
    simpa using hloss.neg
  have hexp_loss :
      Tendsto
        (fun n : ℕ =>
          Real.exp (-(rate (m n) + delta n / (1 - delta n))))
        atTop (nhds 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp hneg_loss
    simpa using h
  let effectiveBase : ℕ → ℝ := fun n =>
    B * Real.exp (-(rate (m n) + delta n / (1 - delta n)))
  have heffective : Tendsto effectiveBase atTop (nhds B) := by
    have hconst : Tendsto (fun _ : ℕ => B) atTop (nhds B) :=
      tendsto_const_nhds
    simpa [effectiveBase] using hconst.mul hexp_loss
  have hdelta_lt_one : ∀ᶠ n : ℕ in atTop, delta n < 1 :=
    (tendsto_order.1 hdelta).2 1 zero_lt_one
  have hm_one : ∀ᶠ n : ℕ in atTop, 1 ≤ m n :=
    hm.eventually (eventually_ge_atTop 1)
  have hV_effective : ∀ᶠ n : ℕ in atTop, V < effectiveBase n :=
    (tendsto_order.1 heffective).1 V hV_lt
  refine ⟨m, hm, ?_⟩
  filter_upwards
      [hm.eventually hrate_extract, hdelta_lt_one, hm_one, hV_effective]
      with n hn_extract hn_delta_lt hn_m hn_effective
  obtain ⟨kc, xc, yc, zc, hc_restrict, hc_weight⟩ := hwitness n
  obtain ⟨k, x, y, z, hrestrict, hweight⟩ :=
    hn_extract (delta n) (hdelta_pos n) hn_delta_lt
      kc xc yc zc hc_restrict hc_weight
  refine ⟨mme_CW_2376_integer_profile (m n), k, x, y, z, hrestrict, ?_⟩
  calc
    V ^ (3000000 * m n)
        ≤ (effectiveBase n) ^ (3000000 * m n) :=
      pow_le_pow_left₀ hV_nonneg hn_effective.le _
    _ ≤ (B * Real.exp (-(rate (m n)))) ^ (3000000 * m n) *
          (1 - delta n) ^ (616627 : ℕ) := by
      exact mme_CW_2376_amplified_error_absorbed
        B (rate (m n)) (delta n) (m n)
        hB_pos.le (hdelta_pos n).le hn_delta_lt hn_m
    _ ≤ ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
      simpa [B] using hweight
