-- Prove2me | solution 1 for Erdos390.Full.FriableAsymptotic.dickmanWeight_pnt_bound
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T14:45:46.906345+00:00
-- url     : https://prove2.me/submissions/eedcdc50-0406-41bf-a21d-48bc4a1e4300

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/









theorem dickmanContinuousWeight_nat (X m : ℕ) :
    dickmanContinuousWeight (X : ℝ) (m : ℝ) =
      dickmanThetaWeight X m := by
  simp only [dickmanContinuousWeight, dickmanThetaWeight,
    dickmanPrimeSummand]









































/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic





theorem deriv_invMulLog {t : ℝ} (ht : t ≠ 0)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt invMulLog
      (-(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) t := by
  unfold invMulLog
  have hden : HasDerivAt (fun s : ℝ => s * Real.log s)
      (Real.log t + 1) t := by
    simpa [ht] using (hasDerivAt_id t).mul (Real.hasDerivAt_log ht)
  have hraw := (hasDerivAt_const t (1 : ℝ)).div hden (mul_ne_zero ht hlog)
  convert hraw using 1
  field_simp [ht, hlog]
  ring

theorem deriv_logRatio (X : ℝ) {t : ℝ} (ht : t ≠ 0)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt (logRatio X)
      (-(Real.log X) / (t * (Real.log t) ^ 2)) t := by
  unfold logRatio
  have hraw := (hasDerivAt_const t (Real.log X)).div
    (Real.hasDerivAt_log ht) hlog
  convert hraw using 1
  field_simp [ht, hlog]
  ring

theorem inv_deriv_bound {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : (k : ℝ) ≤ t) :
    |-(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)| ≤
      6 / (k : ℝ) ^ 2 := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkt : (2 : ℝ) ≤ t := hkreal.trans ht
  have htpos : 0 < t := by linarith
  have hkposNat : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2) hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := by
    have hlogmono : Real.log 2 ≤ Real.log t := by
      apply Real.log_le_log
      · norm_num
      · exact hkt
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  rw [abs_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ Real.log t + 1),
    abs_mul]
  simp only [abs_pow, abs_of_pos htpos, abs_of_pos hlogpos]
  have hpoly : (Real.log t + 1) / (Real.log t) ^ 2 ≤ 6 := by
    apply (div_le_iff₀ (sq_pos_of_pos hlogpos)).2
    nlinarith [sq_nonneg (Real.log t - 1 / 2)]
  calc
    (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) =
        ((Real.log t + 1) / Real.log t ^ 2) / t ^ 2 := by field_simp
    _ ≤ 6 / t ^ 2 := by
      exact div_le_div_of_nonneg_right hpoly (sq_nonneg t)
    _ ≤ 6 / (k : ℝ) ^ 2 := by
      gcongr

theorem logRatio_deriv_bound (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : (k : ℝ) ≤ t) :
    |-(Real.log X) / (t * (Real.log t) ^ 2)| ≤
      4 * Real.log X / (k : ℝ) := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkt : (2 : ℝ) ≤ t := hkreal.trans ht
  have htpos : 0 < t := by linarith
  have hkposNat : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2) hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := by
    have hlogmono : Real.log 2 ≤ Real.log t := by
      apply Real.log_le_log
      · norm_num
      · exact hkt
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  rw [abs_div, abs_neg, abs_of_nonneg hlogX, abs_mul,
    abs_of_pos htpos, abs_pow, abs_of_pos hlogpos]
  have hlogsq : (1 / 4 : ℝ) ≤ Real.log t ^ 2 := by nlinarith
  apply (div_le_div_iff₀ (mul_pos htpos (sq_pos_of_pos hlogpos)) hkpos).2
  have hden1 : t * (1 / 4 : ℝ) ≤ t * Real.log t ^ 2 :=
    mul_le_mul_of_nonneg_left hlogsq htpos.le
  have hden : (k : ℝ) ≤ 4 * (t * Real.log t ^ 2) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hden hlogX]

theorem invMulLog_cell_lipschitz {k : ℕ} (hk : 2 ≤ k)
    {s t : ℝ} (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
    |invMulLog s - invMulLog t| ≤
      (6 / (k : ℝ) ^ 2) * |s - t| := by
  have hdiff (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      DifferentiableAt ℝ invMulLog u := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (deriv_invMulLog hu0 hlogu).differentiableAt
  have hbound (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      ‖deriv invMulLog u‖ ≤ 6 / (k : ℝ) ^ 2 := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    rw [(deriv_invMulLog hu0 hlogu).deriv, Real.norm_eq_abs]
    exact inv_deriv_bound hk hu.1
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (k : ℝ) (k + 1 : ℕ)) ht hs

theorem logRatio_cell_lipschitz (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k)
    {s t : ℝ} (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
    |logRatio X s - logRatio X t| ≤
      (4 * Real.log X / (k : ℝ)) * |s - t| := by
  have hdiff (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      DifferentiableAt ℝ (logRatio X) u := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (deriv_logRatio X hu0 hlogu).differentiableAt
  have hbound (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      ‖deriv (logRatio X) u‖ ≤ 4 * Real.log X / (k : ℝ) := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    rw [(deriv_logRatio X hu0 hlogu).deriv, Real.norm_eq_abs]
    exact logRatio_deriv_bound X hX hk hu.1
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (k : ℝ) (k + 1 : ℕ)) ht hs

theorem invMulLog_bound {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : (k : ℝ) ≤ t) :
    0 ≤ invMulLog t ∧ invMulLog t ≤ 2 / (k : ℝ) := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkt : (2 : ℝ) ≤ t := hkreal.trans ht
  have htpos : 0 < t := by linarith
  have hkposNat : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2) hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := by
    have hlogmono : Real.log 2 ≤ Real.log t := by
      apply Real.log_le_log
      · norm_num
      · exact hkt
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  constructor
  · unfold invMulLog
    positivity
  · unfold invMulLog
    apply (div_le_iff₀ (mul_pos htpos hlogpos)).2
    rw [show 2 / (k : ℝ) * (t * Real.log t) =
      (2 * (t * Real.log t)) / (k : ℝ) by ring]
    apply (le_div_iff₀ hkpos).2
    have hprod : t * (1 / 2 : ℝ) ≤ t * Real.log t :=
      mul_le_mul_of_nonneg_left hlog htpos.le
    nlinarith

theorem rho_logRatio_lipschitz (X s t : ℝ)
    (hs5 : logRatio X s - 1 ≤ 5)
    (ht5 : logRatio X t - 1 ≤ 5) :
    |rho (logRatio X s - 1) - rho (logRatio X t - 1)| ≤
      |logRatio X s - logRatio X t| := by
  by_cases hst : logRatio X t - 1 ≤ logRatio X s - 1
  · have h := rho_lipschitz_of_le_five hst hs5
    calc
      |rho (logRatio X s - 1) - rho (logRatio X t - 1)| ≤
          (logRatio X s - 1) - (logRatio X t - 1) := h
      _ = logRatio X s - logRatio X t := by ring
      _ = |logRatio X s - logRatio X t| := by
        rw [abs_of_nonneg (by linarith)]
  · have h := rho_lipschitz_of_le_five (le_of_not_ge hst) ht5
    rw [abs_sub_comm]
    calc
      |rho (logRatio X t - 1) - rho (logRatio X s - 1)| ≤
          (logRatio X t - 1) - (logRatio X s - 1) := h
      _ = logRatio X t - logRatio X s := by ring
      _ = |logRatio X t - logRatio X s| := by
        rw [abs_of_nonneg (by linarith)]
      _ = |logRatio X s - logRatio X t| := abs_sub_comm _ _

theorem dickmanContinuousWeight_cell_lipschitz (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k) {s t : ℝ}
    (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (hqs0 : 0 ≤ logRatio X s - 1) (hqs5 : logRatio X s - 1 ≤ 5)
    (hqt5 : logRatio X t - 1 ≤ 5) :
    |dickmanContinuousWeight X s - dickmanContinuousWeight X t| ≤
      (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) * |s - t| := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hA_t := invMulLog_bound hk ht.1
  have hAdiff := invMulLog_cell_lipschitz hk hs ht
  have hQdiff := logRatio_cell_lipschitz X hX hk hs ht
  have hRdiff := (rho_logRatio_lipschitz X s t hqs5 hqt5).trans hQdiff
  have hRspos : 0 ≤ rho (logRatio X s - 1) :=
    (rho_pos_on_zero_five hqs0 hqs5).le
  have hRsle : rho (logRatio X s - 1) ≤ 1 :=
    rho_le_one_of_le_five hqs5
  have hAstabs : |invMulLog t| ≤ 2 / (k : ℝ) := by
    rw [abs_of_nonneg hA_t.1]
    exact hA_t.2
  have hrewrite (u : ℝ) :
      dickmanContinuousWeight X u =
        X * invMulLog u * rho (logRatio X u - 1) := by
    unfold dickmanContinuousWeight invMulLog logRatio
    ring
  rw [hrewrite, hrewrite]
  have halgebra :
      invMulLog s * rho (logRatio X s - 1) -
          invMulLog t * rho (logRatio X t - 1) =
        (invMulLog s - invMulLog t) * rho (logRatio X s - 1) +
          invMulLog t * (rho (logRatio X s - 1) -
            rho (logRatio X t - 1)) := by ring
  have hfactor :
      X * invMulLog s * rho (logRatio X s - 1) -
          X * invMulLog t * rho (logRatio X t - 1) =
        X * (invMulLog s * rho (logRatio X s - 1) -
          invMulLog t * rho (logRatio X t - 1)) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg hX0, halgebra]
  calc
    X * |(invMulLog s - invMulLog t) * rho (logRatio X s - 1) +
        invMulLog t * (rho (logRatio X s - 1) -
          rho (logRatio X t - 1))| ≤
      X * (|invMulLog s - invMulLog t| *
          |rho (logRatio X s - 1)| +
        |invMulLog t| * |rho (logRatio X s - 1) -
          rho (logRatio X t - 1)|) := by
      apply mul_le_mul_of_nonneg_left _ hX0
      simpa only [abs_mul] using abs_add_le
        ((invMulLog s - invMulLog t) * rho (logRatio X s - 1))
        (invMulLog t * (rho (logRatio X s - 1) -
          rho (logRatio X t - 1)))
    _ ≤ X * ((6 / (k : ℝ) ^ 2 * |s - t|) * 1 +
        (2 / (k : ℝ)) * ((4 * Real.log X / (k : ℝ)) * |s - t|)) := by
      have hRsabs : |rho (logRatio X s - 1)| ≤ 1 := by
        rw [abs_of_nonneg hRspos]
        exact hRsle
      have hBnonneg : 0 ≤ 6 / (k : ℝ) ^ 2 * |s - t| := by positivity
      have hCnonneg : 0 ≤ 2 / (k : ℝ) := by positivity
      have hterm1 :
          |invMulLog s - invMulLog t| * |rho (logRatio X s - 1)| ≤
            (6 / (k : ℝ) ^ 2 * |s - t|) * 1 :=
        mul_le_mul hAdiff hRsabs (abs_nonneg _) hBnonneg
      have hterm2 :
          |invMulLog t| * |rho (logRatio X s - 1) -
              rho (logRatio X t - 1)| ≤
            (2 / (k : ℝ)) *
              ((4 * Real.log X / (k : ℝ)) * |s - t|) :=
        mul_le_mul hAstabs hRdiff (abs_nonneg _) hCnonneg
      exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hX0
    _ = (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) * |s - t| := by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      field_simp
      ring

theorem dickmanContinuousWeight_cell_oscillation (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (hq : ∀ u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ),
      0 ≤ logRatio X u - 1 ∧ logRatio X u - 1 ≤ 5) :
    |dickmanContinuousWeight X (k + 1 : ℕ) -
        dickmanContinuousWeight X t| ≤
      X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2 := by
  have hs : ((k + 1 : ℕ) : ℝ) ∈
      Set.Icc (k : ℝ) (k + 1 : ℕ) := by constructor <;> norm_num
  have h := dickmanContinuousWeight_cell_lipschitz X hX hk hs ht
    (hq _ hs).1 (hq _ hs).2 (hq _ ht).2
  have hdist : |((k + 1 : ℕ) : ℝ) - t| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [ht.2])]
    norm_num
    linarith [ht.1]
  have hcoef : 0 ≤ X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2 := by
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
    positivity
  calc
    |dickmanContinuousWeight X (k + 1 : ℕ) -
        dickmanContinuousWeight X t| ≤
      (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) *
        |((k + 1 : ℕ) : ℝ) - t| := h
    _ ≤ (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) * 1 := by
      exact mul_le_mul_of_nonneg_left hdist hcoef
    _ = _ := by ring






/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/

theorem continuousWeight_eq (X t : ℝ) :
    dickmanContinuousWeight X t =
      X * invMulLog t * rho (logRatio X t - 1) := by
  unfold dickmanContinuousWeight invMulLog logRatio
  ring

theorem thetaWeight_abs_le (X m : ℕ) (hX : 1 ≤ X) (hm : 2 ≤ m)
    (hq0 : 1 ≤ logRatio (X : ℝ) (m : ℝ))
    (hq6 : logRatio (X : ℝ) (m : ℝ) ≤ 6) :
    |dickmanThetaWeight X m| ≤ 2 * (X : ℝ) / (m : ℝ) := by
  rw [← dickmanContinuousWeight_nat, continuousWeight_eq, abs_mul, abs_mul]
  have hXR : (0 : ℝ) ≤ X := by positivity
  have hA := invMulLog_bound hm (le_refl (m : ℝ))
  have hRpos : 0 ≤ rho (logRatio (X : ℝ) (m : ℝ) - 1) :=
    (rho_pos_on_zero_five (by linarith) (by linarith)).le
  have hRle : rho (logRatio (X : ℝ) (m : ℝ) - 1) ≤ 1 :=
    rho_le_one_of_le_five (by linarith)
  rw [abs_of_nonneg hXR, abs_of_nonneg hA.1, abs_of_nonneg hRpos]
  calc
    (X : ℝ) * invMulLog (m : ℝ) * rho (logRatio (X : ℝ) (m : ℝ) - 1) =
        (X : ℝ) * (invMulLog (m : ℝ) *
          rho (logRatio (X : ℝ) (m : ℝ) - 1)) := by ring
    _ ≤ (X : ℝ) * ((2 / (m : ℝ)) * 1) := by
      apply mul_le_mul_of_nonneg_left _ hXR
      exact mul_le_mul hA.2 hRle hRpos (by positivity)
    _ = 2 * (X : ℝ) / (m : ℝ) := by ring



theorem thetaWeight_diff_bound (X : ℕ) (hX : 1 ≤ X)
    {m : ℕ} (hm : 2 ≤ m)
    (hq : ∀ u ∈ Set.Icc (m : ℝ) (m + 1 : ℕ),
      1 ≤ logRatio (X : ℝ) u ∧ logRatio (X : ℝ) u ≤ 6) :
    |dickmanThetaWeight X (m + 1) - dickmanThetaWeight X m| ≤
      (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (m : ℝ) ^ 2 := by
  rw [← dickmanContinuousWeight_nat, ← dickmanContinuousWeight_nat]
  have ht : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + 1 : ℕ) := by
    constructor <;> norm_num
  apply dickmanContinuousWeight_cell_oscillation
    (X : ℝ) (by exact_mod_cast hX) hm ht
  intro u hu
  have huq := hq u hu
  exact ⟨by linarith [huq.1], by linarith [huq.2]⟩

set_option maxHeartbeats 800000 in
theorem dickmanWeight_pnt_bound (X : ℕ) (hX : 1 ≤ X)
    {C : ℝ} (hC : 0 ≤ C) {X₀ z y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / (Real.log (T : ℝ)) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6) :
    |primeThetaWeightedInterval (dickmanThetaWeight X) z y -
        integerAbelMain (dickmanThetaWeight X) z y| ≤
      500 * C * (X : ℝ) / Real.log (z : ℝ) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hz.trans hzy.le
  have hlogz : (1 / 2 : ℝ) ≤ Real.log (z : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (z : ℝ) := by
      apply Real.log_le_log
      · norm_num
      · exact hzR
    nlinarith [Real.log_two_gt_d9]
  have hlogzpos : 0 < Real.log (z : ℝ) := by linarith
  have hlogypos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hlogzy : Real.log (z : ℝ) ≤ Real.log (y : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hzy.le
  have hzmem : (z : ℝ) ∈ Set.Icc (z : ℝ) (y : ℝ) :=
    ⟨le_rfl, by exact_mod_cast hzy.le⟩
  have hymem : (y : ℝ) ∈ Set.Icc (z : ℝ) (y : ℝ) :=
    ⟨by exact_mod_cast hzy.le, le_rfl⟩
  have hlogX_le : Real.log (X : ℝ) ≤ 6 * Real.log (z : ℝ) := by
    have hzq := (hq _ hzmem).2
    rw [logRatio] at hzq
    exact (div_le_iff₀ hlogzpos).mp hzq
  have hlogy_le : Real.log (y : ℝ) ≤ Real.log (X : ℝ) := by
    have hyq := (hq _ hymem).1
    rw [logRatio] at hyq
    simpa using (le_div_iff₀ hlogypos).mp hyq
  have hone_logy : 1 + Real.log (y : ℝ) ≤ 8 * Real.log (z : ℝ) := by
    linarith
  have hinv3 : 1 / Real.log (z : ℝ) ^ 3 ≤ 4 / Real.log (z : ℝ) := by
    apply (div_le_div_iff₀ (pow_pos hlogzpos 3) hlogzpos).2
    nlinarith [sq_nonneg (Real.log (z : ℝ) - 1 / 2)]
  have hgeneric := primeThetaWeightedInterval_pnt_bound
    (dickmanThetaWeight X) (A := (3 : ℝ)) hbound hX₀z hzy
  simp only [Real.rpow_ofNat] at hgeneric
  have hfy := thetaWeight_abs_le X y hX (hz.trans hzy.le) (hq _ hymem).1 (hq _ hymem).2
  have hz1mem : ((z + 1 : ℕ) : ℝ) ∈ Set.Icc (z : ℝ) (y : ℝ) := by
    constructor
    · norm_num
    · exact_mod_cast (by omega : z + 1 ≤ y)
  have hfz1raw := thetaWeight_abs_le X (z + 1) hX (by omega)
    (hq _ hz1mem).1 (hq _ hz1mem).2
  have hfz1 : |dickmanThetaWeight X (z + 1)| ≤
      2 * (X : ℝ) / (z : ℝ) := by
    exact hfz1raw.trans (by gcongr; omega)
  have htermY :
      |dickmanThetaWeight X y| *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ (3 : ℕ))) ≤
        8 * C * (X : ℝ) / Real.log (z : ℝ) := by
    calc
      _ ≤ (2 * (X : ℝ) / (y : ℝ)) *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ (3 : ℕ))) := by
        gcongr
      _ = 2 * C * (X : ℝ) / Real.log (y : ℝ) ^ 3 := by
        have hy0 : (y : ℝ) ≠ 0 := by positivity
        field_simp [hy0]
      _ ≤ 2 * C * (X : ℝ) / Real.log (z : ℝ) ^ 3 := by
        gcongr
      _ ≤ 8 * C * (X : ℝ) / Real.log (z : ℝ) := by
        have hfac : 0 ≤ 2 * C * (X : ℝ) := by positivity
        calc
          _ = (2 * C * (X : ℝ)) *
              (1 / Real.log (z : ℝ) ^ 3) := by ring
          _ ≤ (2 * C * (X : ℝ)) *
              (4 / Real.log (z : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv3 hfac
          _ = _ := by ring
  have htermZ :
      |dickmanThetaWeight X (z + 1)| *
          (C * ((z : ℝ) / Real.log (z : ℝ) ^ (3 : ℕ))) ≤
        8 * C * (X : ℝ) / Real.log (z : ℝ) := by
    calc
      _ ≤ (2 * (X : ℝ) / (z : ℝ)) *
          (C * ((z : ℝ) / Real.log (z : ℝ) ^ (3 : ℕ))) := by
        gcongr
      _ = 2 * C * (X : ℝ) / Real.log (z : ℝ) ^ 3 := by
        have hz0 : (z : ℝ) ≠ 0 := by positivity
        field_simp [hz0]
      _ ≤ 8 * C * (X : ℝ) / Real.log (z : ℝ) := by
        have hfac : 0 ≤ 2 * C * (X : ℝ) := by positivity
        calc
          _ = (2 * C * (X : ℝ)) *
              (1 / Real.log (z : ℝ) ^ 3) := by ring
          _ ≤ (2 * C * (X : ℝ)) *
              (4 / Real.log (z : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv3 hfac
          _ = _ := by ring
  have hvar :
      (∑ m ∈ Finset.Ioc z (y - 1),
        |dickmanThetaWeight X (m + 1) - dickmanThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ (3 : ℕ)))) ≤
        480 * C * (X : ℝ) / Real.log (z : ℝ) := by
    let K : ℝ := 6 + 8 * Real.log (X : ℝ)
    have hlogXnonneg : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXR
    have hKnonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    have hKle : K ≤ 6 + 48 * Real.log (z : ℝ) := by
      dsimp [K]
      nlinarith
    have hinv2 : 1 / Real.log (z : ℝ) ^ 2 ≤
        2 / Real.log (z : ℝ) := by
      apply (div_le_div_iff₀ (pow_pos hlogzpos 2) hlogzpos).2
      nlinarith [sq_nonneg (Real.log (z : ℝ) - 1 / 2)]
    have hpoint : ∀ m ∈ Finset.Ioc z (y - 1),
        |dickmanThetaWeight X (m + 1) - dickmanThetaWeight X m| *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3)) ≤
          (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
            (1 / (m : ℝ)) := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      have hm2 : 2 ≤ m := by omega
      have hm1y : m + 1 ≤ y := by omega
      have hqcell : ∀ u ∈ Set.Icc (m : ℝ) (m + 1 : ℕ),
          1 ≤ logRatio (X : ℝ) u ∧ logRatio (X : ℝ) u ≤ 6 := by
        intro u hu
        apply hq u
        constructor
        · calc
            (z : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1.le
            _ ≤ u := hu.1
        · calc
            u ≤ ((m + 1 : ℕ) : ℝ) := hu.2
            _ ≤ (y : ℝ) := by exact_mod_cast hm1y
      have hdiff := thetaWeight_diff_bound X hX hm2 hqcell
      have hlogmpos : 0 < Real.log (m : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      have hlogzm : Real.log (z : ℝ) ≤ Real.log (m : ℝ) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast hm.1.le
      have hinvlog : 1 / Real.log (m : ℝ) ^ 3 ≤
          1 / Real.log (z : ℝ) ^ 3 := by
        gcongr
      have hfactor : 0 ≤ C * ((m : ℝ) / Real.log (m : ℝ) ^ 3) := by
        positivity
      calc
        _ ≤ ((X : ℝ) * K / (m : ℝ) ^ 2) *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3)) := by
          exact mul_le_mul_of_nonneg_right hdiff hfactor
        _ = (C * (X : ℝ) * K *
              (1 / Real.log (m : ℝ) ^ 3)) * (1 / (m : ℝ)) := by
          have hm0 : (m : ℝ) ≠ 0 := by positivity
          field_simp
        _ ≤ (C * (X : ℝ) * K *
              (1 / Real.log (z : ℝ) ^ 3)) * (1 / (m : ℝ)) := by
          gcongr
        _ = (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
              (1 / (m : ℝ)) := by ring
    have hsum :
        (∑ m ∈ Finset.Ioc z (y - 1),
          |dickmanThetaWeight X (m + 1) - dickmanThetaWeight X m| *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3))) ≤
          (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
            (∑ m ∈ Finset.Ioc z (y - 1), 1 / (m : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun m hm => hpoint m hm
    have hhar : (∑ m ∈ Finset.Ioc z (y - 1), 1 / (m : ℝ)) ≤
        1 + Real.log (y : ℝ) := by
      calc
        _ ≤ ∑ m ∈ Finset.Ioc z y, 1 / (m : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            rw [Finset.mem_Ioc] at hm ⊢
            omega
          · intro m hm hmn
            positivity
        _ ≤ 1 + Real.log (y : ℝ) := harmonic_Ioc_le
    calc
      _ ≤ (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
          (∑ m ∈ Finset.Ioc z (y - 1), 1 / (m : ℝ)) := hsum
      _ ≤ (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
          (1 + Real.log (y : ℝ)) := by gcongr
      _ ≤ (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
          (8 * Real.log (z : ℝ)) := by gcongr
      _ = 8 * C * (X : ℝ) * K / Real.log (z : ℝ) ^ 2 := by
        field_simp
      _ ≤ 8 * C * (X : ℝ) *
          (6 + 48 * Real.log (z : ℝ)) /
            Real.log (z : ℝ) ^ 2 := by gcongr
      _ = 48 * C * (X : ℝ) / Real.log (z : ℝ) ^ 2 +
          384 * C * (X : ℝ) / Real.log (z : ℝ) := by
        field_simp
        ring
      _ ≤ 480 * C * (X : ℝ) / Real.log (z : ℝ) := by
        have hfac : 0 ≤ 48 * C * (X : ℝ) := by positivity
        calc
          _ = (48 * C * (X : ℝ)) *
                (1 / Real.log (z : ℝ) ^ 2) +
              384 * C * (X : ℝ) / Real.log (z : ℝ) := by ring
          _ ≤ (48 * C * (X : ℝ)) *
                (2 / Real.log (z : ℝ)) +
              384 * C * (X : ℝ) / Real.log (z : ℝ) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hinv2 hfac) le_rfl
          _ = _ := by ring
  calc
    _ ≤ |dickmanThetaWeight X y| *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ (3 : ℕ))) +
        |dickmanThetaWeight X (z + 1)| *
          (C * ((z : ℝ) / Real.log (z : ℝ) ^ (3 : ℕ))) +
        ∑ m ∈ Finset.Ioc z (y - 1),
          |dickmanThetaWeight X (m + 1) - dickmanThetaWeight X m| *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ (3 : ℕ))) := hgeneric
    _ ≤ 8 * C * (X : ℝ) / Real.log (z : ℝ) +
        8 * C * (X : ℝ) / Real.log (z : ℝ) +
        480 * C * (X : ℝ) / Real.log (z : ℝ) := by
      exact add_le_add (add_le_add htermY htermZ) hvar
    _ = 496 * C * (X : ℝ) / Real.log (z : ℝ) := by ring
    _ ≤ 500 * C * (X : ℝ) / Real.log (z : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlogzpos.le
      have hCX : 0 ≤ C * (X : ℝ) := by positivity
      nlinarith








/-! ## Uniform floor stability for the recursive Dickman kernel -/





























































end Erdos390.Full.FriableAsymptotic

end

theorem solution :
∀ (X : Nat),
  LE.le.{0} (1 : Nat) X →
    ∀ {C : Real},
      LE.le.{0} (0 : Real) C →
        ∀ {X₀ z y : Nat},
          (∀ (T : Nat),
              LE.le.{0} X₀ T →
                LE.le.{0} (abs.{0} (HSub.hSub.{0, 0, 0} (Erdos390.Full.FriableAsymptotic.primeLogSumUpTo T) ↑T))
                  (HMul.hMul.{0, 0, 0} C (HDiv.hDiv.{0, 0, 0} (↑T) (HPow.hPow.{0, 0, 0} (Real.log ↑T) (3 : Real))))) →
            LE.le.{0} X₀ z →
              LE.le.{0} (2 : Nat) z →
                LT.lt.{0} z y →
                  (∀ (t : Real),
                      Membership.mem.{0, 0} (Set.Icc.{0} ↑z ↑y) t →
                        And (LE.le.{0} (1 : Real) (Erdos390.Full.FriableAsymptotic.logRatio (↑X) t))
                          (LE.le.{0} (Erdos390.Full.FriableAsymptotic.logRatio (↑X) t) (6 : Real))) →
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FriableAsymptotic.primeThetaWeightedInterval
                            (Erdos390.Full.FriableAsymptotic.dickmanThetaWeight X) z y)
                          (Erdos390.Full.FriableAsymptotic.integerAbelMain
                            (Erdos390.Full.FriableAsymptotic.dickmanThetaWeight X) z y)))
                      (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (500 : Real) C) ↑X) (Real.log ↑z)) := by
  exact @Erdos390.Full.FriableAsymptotic.dickmanWeight_pnt_bound
