-- Prove2me | solution 1 for mme_dwz_multinomial_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:50:51.75647+00:00
-- url     : https://prove2.me/submissions/85d2fcf3-8a33-4a77-a82e-9229ef3008f1

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open scoped BigOperators

set_option autoImplicit false

namespace MME.DWZMultinomialEntropyUpper

/-- The natural-log entropy weight of an integral histogram. -/
noncomputable def entropyWeight {R : Type*} [Fintype R] (w : R → ℕ) : ℝ :=
  let W := ∑ i, w i
  (W : ℝ) * Real.log (W : ℝ) -
    ∑ i, (w i : ℝ) * Real.log (w i : ℝ)

theorem entropyWeight_eq_bits
    {R : Type*} [Fintype R] (w : R → ℕ)
    (hW : 0 < ∑ i, w i) :
    entropyWeight w =
      ((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
        mme_modern_entropyBits
          (fun i ↦ (w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)) := by
  classical
  let W : ℕ := ∑ i, w i
  have hWR : (W : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hW)
  have hsumR : (∑ i, (w i : ℝ)) ≠ 0 := by
    rw [← Nat.cast_sum]
    simpa only [W] using hWR
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold entropyWeight mme_modern_entropyBits
  dsimp only
  rw [mul_assoc, mul_div_cancel₀ _ hlog2]
  rw [Finset.mul_sum]
  rw [Nat.cast_sum, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hwi : w i = 0
  · simp [hwi]
  · have hwiR : (w i : ℝ) ≠ 0 := by exact_mod_cast hwi
    simp only [Real.negMulLog_def]
    rw [Real.log_div hwiR hsumR]
    field_simp
    ring

private theorem entropy_probability_cancel
    {R : Type*} [Fintype R] (w : R → ℕ)
    (m : ℕ) (hm : 0 < m) (hW : 0 < ∑ i, w i) :
    Real.exp ((m : ℝ) * entropyWeight w) *
        (∏ i, ((w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)) ^ (w i * m)) =
      1 := by
  classical
  let W : ℕ := ∑ i, w i
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfactor_pos (i : R) :
      0 < ((w i : ℝ) / (W : ℝ)) ^ (w i * m) := by
    by_cases hwi : w i = 0
    · simp [hwi]
    · have hwiR : (0 : ℝ) < w i := by exact_mod_cast (Nat.pos_of_ne_zero hwi)
      positivity
  have hprod_pos :
      0 < ∏ i, ((w i : ℝ) / (W : ℝ)) ^ (w i * m) := by
    exact Finset.prod_pos fun i _ ↦ hfactor_pos i
  apply Real.log_injOn_pos (mul_pos (Real.exp_pos _) hprod_pos) (by norm_num)
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hprod_pos), Real.log_exp,
    Real.log_one]
  rw [Real.log_prod (fun i _ ↦ ne_of_gt (hfactor_pos i))]
  have hlogFactor (i : R) :
      Real.log (((w i : ℝ) / (W : ℝ)) ^ (w i * m)) =
        ((w i : ℝ) * (m : ℝ)) *
          (Real.log (w i : ℝ) - Real.log (W : ℝ)) := by
    by_cases hwi : w i = 0
    · simp [hwi]
    · have hwiR : (w i : ℝ) ≠ 0 := by exact_mod_cast hwi
      rw [Real.log_pow, Real.log_div hwiR (ne_of_gt hWR)]
      push_cast
      ring
  simp_rw [hlogFactor]
  have hsum :
      (∑ i, ((w i : ℝ) * (m : ℝ)) *
          (Real.log (w i : ℝ) - Real.log (W : ℝ))) =
        (m : ℝ) * (∑ i, (w i : ℝ) * Real.log (w i : ℝ)) -
          (m : ℝ) * (W : ℝ) * Real.log (W : ℝ) := by
    calc
      (∑ i, ((w i : ℝ) * (m : ℝ)) *
          (Real.log (w i : ℝ) - Real.log (W : ℝ))) =
          ∑ i, ((m : ℝ) * ((w i : ℝ) * Real.log (w i : ℝ)) -
            ((m : ℝ) * Real.log (W : ℝ)) * (w i : ℝ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (m : ℝ) * (∑ i, (w i : ℝ) * Real.log (w i : ℝ)) -
          (m : ℝ) * (W : ℝ) * Real.log (W : ℝ) := by
            rw [Finset.sum_sub_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
            rw [← Nat.cast_sum]
            ring
  rw [hsum]
  unfold entropyWeight
  dsimp only
  simp only [W]
  ring

theorem multinomial_entropy_upper
    {R : Type*} [Fintype R] (w : R → ℕ)
    (m : ℕ) (hm : 0 < m) (hW : 0 < ∑ i, w i) :
    (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) ≤
      Real.exp ((m : ℝ) * entropyWeight w) := by
  classical
  let W : ℕ := ∑ i, w i
  let N : ℕ := W * m
  let p : R → ℝ := fun i ↦ (w i : ℝ) / (W : ℝ)
  let c : R → ℕ := fun i ↦ w i * m
  let P : ℝ := ∏ i, p i ^ c i
  let V : ℝ := Nat.multinomial Finset.univ c
  have hWR : (W : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hW)
  have hp_sum : ∑ i, p i = 1 := by
    dsimp [p]
    rw [← Finset.sum_div, ← Nat.cast_sum]
    exact div_self hWR
  have hc_sum : ∑ i, c i = N := by
    dsimp [c, N, W]
    rw [← Finset.sum_mul]
  have hc_mem : c ∈ Finset.piAntidiag Finset.univ N := by
    rw [Finset.mem_piAntidiag]
    exact ⟨by simpa using hc_sum, fun i hi ↦ Finset.mem_univ i⟩
  have hterm_nonneg (k : R → ℕ) :
      0 ≤ (Nat.multinomial Finset.univ k : ℝ) *
        ∏ i, p i ^ k i := by
    dsimp [p]
    positivity
  have hterm : V * P ≤
      ∑ k ∈ Finset.piAntidiag Finset.univ N,
        (Nat.multinomial Finset.univ k : ℝ) * ∏ i, p i ^ k i := by
    dsimp [V, P]
    exact Finset.single_le_sum (fun k _ ↦ hterm_nonneg k) hc_mem
  have hexpand :=
    Finset.sum_pow_eq_sum_piAntidiag (R := ℝ) Finset.univ p N
  have hprob : V * P ≤ 1 := by
    calc
      V * P ≤ ∑ k ∈ Finset.piAntidiag Finset.univ N,
          (Nat.multinomial Finset.univ k : ℝ) * ∏ i, p i ^ k i := hterm
      _ = (∑ i ∈ Finset.univ, p i) ^ N := hexpand.symm
      _ = 1 := by simp only [hp_sum, one_pow]
  have hPpos : 0 < P := by
    dsimp [P, p, c]
    have hWRpos : (0 : ℝ) < W := by exact_mod_cast hW
    apply Finset.prod_pos
    intro i hi
    by_cases hwi : w i = 0
    · simp [hwi]
    · have hwiR : (0 : ℝ) < w i := by exact_mod_cast (Nat.pos_of_ne_zero hwi)
      positivity
  have hcancel : Real.exp ((m : ℝ) * entropyWeight w) * P = 1 := by
    dsimp [P, p, c, W]
    exact entropy_probability_cancel w m hm hW
  apply le_of_mul_le_mul_right _ hPpos
  calc
    V * P ≤ 1 := hprob
    _ = Real.exp ((m : ℝ) * entropyWeight w) * P := hcancel.symm

/-- Division-free entropy upper bound for a fiber count obtained from a
multinomial factorization.  This is the analytic form consumed by the typical
block denominator in DWZ Lemma 6.7. -/
theorem typical_denominator_entropy_upper_of_factorization
    {Fine Coarse : Type*} [Fintype Fine] [Fintype Coarse]
    (gamma : Fine → ℕ) (alphaZ : Coarse → ℕ)
    (m : ℕ) (hm : 0 < m)
    (hsum : ∑ i, gamma i = ∑ k, alphaZ k)
    (hW : 0 < ∑ i, gamma i)
    (B : ℕ)
    (hfactor :
      Nat.multinomial Finset.univ (fun i ↦ gamma i * m) =
        Nat.multinomial Finset.univ (fun k ↦ alphaZ k * m) * B) :
    (B : ℝ) ≤
      (6 * (((∑ k, alphaZ k) * m + 1 : ℕ) : ℝ)) ^ Fintype.card Coarse *
        Real.exp (
          (m : ℝ) * (((∑ i, gamma i : ℕ) : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (fun i ↦ (gamma i : ℝ) / ((∑ j, gamma j : ℕ) : ℝ))) -
          (m : ℝ) * (((∑ k, alphaZ k : ℕ) : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (fun k ↦ (alphaZ k : ℝ) / ((∑ l, alphaZ l : ℕ) : ℝ)))) := by
  let Eg : ℝ :=
    (m : ℝ) * (((∑ i, gamma i : ℕ) : ℝ) * Real.log 2 *
      mme_modern_entropyBits
        (fun i ↦ (gamma i : ℝ) / ((∑ j, gamma j : ℕ) : ℝ)))
  let Ea : ℝ :=
    (m : ℝ) * (((∑ k, alphaZ k : ℕ) : ℝ) * Real.log 2 *
      mme_modern_entropyBits
        (fun k ↦ (alphaZ k : ℝ) / ((∑ l, alphaZ l : ℕ) : ℝ)))
  let D : ℝ :=
    (6 * (((∑ k, alphaZ k) * m + 1 : ℕ) : ℝ)) ^ Fintype.card Coarse
  let Mg : ℝ := Nat.multinomial Finset.univ (fun i ↦ gamma i * m)
  let Ma : ℝ := Nat.multinomial Finset.univ (fun k ↦ alphaZ k * m)
  have hWa : 0 < ∑ k, alphaZ k := by omega
  have hgUpper : Mg ≤ Real.exp Eg := by
    dsimp [Mg, Eg]
    rw [← entropyWeight_eq_bits gamma hW]
    exact multinomial_entropy_upper gamma m hm hW
  have haLower : Real.exp Ea ≤ D * Ma := by
    dsimp [Ea, D, Ma]
    exact mme_dwz_multinomial_entropy_polynomial_lower alphaZ m hm hWa
  have hfactorR : Mg = Ma * (B : ℝ) := by
    dsimp [Mg, Ma]
    exact_mod_cast hfactor
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity
  change (B : ℝ) ≤ D * Real.exp (Eg - Ea)
  apply le_of_mul_le_mul_left _ (Real.exp_pos Ea)
  calc
    Real.exp Ea * (B : ℝ) ≤ (D * Ma) * (B : ℝ) := by
      gcongr
    _ = D * Mg := by rw [hfactorR]; ring
    _ ≤ D * Real.exp Eg := by gcongr
    _ = Real.exp Ea * (D * Real.exp (Eg - Ea)) := by
      rw [show Real.exp Ea * (D * Real.exp (Eg - Ea)) =
          D * (Real.exp Ea * Real.exp (Eg - Ea)) by ring]
      rw [← Real.exp_add]
      rw [show Ea + (Eg - Ea) = Eg by ring]

end MME.DWZMultinomialEntropyUpper

open MME.DWZMultinomialEntropyUpper

/-- A multinomial coefficient is at most its exact Shannon exponential rate. -/
theorem solution
    {R : Type*} [Fintype R] (w : R → ℕ)
    (m : ℕ) (hm : 0 < m) (hW : 0 < ∑ i, w i) :
    (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) ≤
      Real.exp
        ((m : ℝ) * (((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (fun i ↦ (w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)))) := by
  rw [← entropyWeight_eq_bits w hW]
  exact multinomial_entropy_upper w m hm hW
