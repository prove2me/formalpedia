-- Prove2me | solution 1 for mme_dwz_multinomial_entropy_polynomial_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:24:46.640571+00:00
-- url     : https://prove2.me/submissions/274b1684-14fc-417d-9514-eb4f00c0ccd6

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_modern_entropy_data

open scoped BigOperators
open Filter

set_option autoImplicit false

namespace MME.DWZMultinomialEntropy

private theorem factorial_upper_coarse (n : ℕ) :
    (n.factorial : ℝ) ≤
      6 * ((n + 1 : ℕ) : ℝ) * (((n : ℕ) : ℝ) / Real.exp 1) ^ n := by
  by_cases hn : n = 0
  · subst n
    norm_num
  · let k := n - 1
    have hnk : n = k + 1 := by
      dsimp [k]
      omega
    rw [hnk]
    have hs : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 := by
      simpa [Function.comp_apply] using
        (Stirling.stirlingSeq'_antitone (Nat.zero_le k))
    have hs3 : Stirling.stirlingSeq (k + 1) ≤ 3 := by
      refine hs.trans ?_
      rw [Stirling.stirlingSeq_one]
      refine (_root_.div_le_self (Real.exp_pos 1).le ?_).trans Real.exp_one_lt_three.le
      rw [Real.one_le_sqrt]
      norm_num
    have hden :
        0 < Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) *
          (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by
      positivity
    rw [Stirling.stirlingSeq] at hs3
    have hfac :
        (((k + 1).factorial : ℕ) : ℝ) ≤
          3 * (Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) *
            (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) :=
      (div_le_iff₀ hden).mp hs3
    have hsqrt :
        Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) ≤
          2 * (((k + 1 + 1 : ℕ) : ℝ)) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · push_cast
        nlinarith [sq_nonneg (k : ℝ)]
    calc
      (((k + 1).factorial : ℕ) : ℝ)
          ≤ 3 * (Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) *
            (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) := hfac
      _ ≤ 3 * ((2 * (((k + 1 + 1 : ℕ) : ℝ))) *
            (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) := by
        gcongr
      _ = 6 * (((k + 1 + 1 : ℕ) : ℝ)) *
            (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by ring

private theorem factorial_lower_coarse (n : ℕ) :
    (((n : ℕ) : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  · apply le_trans ?_ (Stirling.le_factorial_stirling n)
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
      rw [Real.one_le_sqrt]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      nlinarith [Real.pi_gt_three]
    have hp : 0 ≤ (((n : ℕ) : ℝ) / Real.exp 1) ^ n := by positivity
    exact le_mul_of_one_le_left hp hsqrt

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

private theorem entropy_cancel
    {R : Type*} [Fintype R] (w : R → ℕ)
    (m : ℕ) (hm : 0 < m) (hW : 0 < ∑ i, w i) :
    Real.exp ((m : ℝ) * entropyWeight w) *
        (∏ i, (((w i * m : ℕ) : ℝ) / Real.exp 1) ^ (w i * m)) =
      ((((∑ i, w i) * m : ℕ) : ℝ) / Real.exp 1) ^
        ((∑ i, w i) * m) := by
  classical
  let W : ℕ := ∑ i, w i
  have hW0 : W ≠ 0 := Nat.ne_of_gt hW
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfactor_pos (i : R) :
      0 < (((w i * m : ℕ) : ℝ) / Real.exp 1) ^ (w i * m) := by
    by_cases hwi : w i = 0
    · simp [hwi]
    · have hwiR : (0 : ℝ) < w i := by exact_mod_cast (Nat.pos_of_ne_zero hwi)
      positivity
  have hprod_pos :
      0 < ∏ i, (((w i * m : ℕ) : ℝ) / Real.exp 1) ^ (w i * m) := by
    exact Finset.prod_pos fun i _ ↦ hfactor_pos i
  have htotal_pos :
      0 < ((((∑ i, w i) * m : ℕ) : ℝ) / Real.exp 1) := by
    positivity
  apply Real.log_injOn_pos (mul_pos (Real.exp_pos _) hprod_pos) (pow_pos htotal_pos _)
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hprod_pos), Real.log_exp]
  rw [Real.log_prod (fun i _ ↦ ne_of_gt (hfactor_pos i))]
  have hlogFactor (i : R) :
      Real.log ((((w i * m : ℕ) : ℝ) / Real.exp 1) ^ (w i * m)) =
        ((w i : ℝ) * (m : ℝ)) *
          (Real.log (w i : ℝ) + Real.log (m : ℝ) - 1) := by
    by_cases hwi : w i = 0
    · simp [hwi]
    · have hwiR : (w i : ℝ) ≠ 0 := by exact_mod_cast hwi
      rw [Real.log_pow, Real.log_div (by positivity) (Real.exp_ne_zero 1),
        Real.log_exp]
      push_cast
      rw [Real.log_mul hwiR (ne_of_gt hmR)]
  simp_rw [hlogFactor]
  have hlogTotal :
      Real.log (((((∑ i, w i) * m : ℕ) : ℝ) / Real.exp 1) ^
          ((∑ i, w i) * m)) =
        ((W : ℝ) * (m : ℝ)) *
          (Real.log (W : ℝ) + Real.log (m : ℝ) - 1) := by
    rw [Real.log_pow, Real.log_div (by positivity) (Real.exp_ne_zero 1),
      Real.log_exp]
    push_cast
    rw [← Nat.cast_sum]
    rw [Real.log_mul (ne_of_gt hWR) (ne_of_gt hmR)]
  rw [hlogTotal]
  have hsum :
      (∑ i, ((w i : ℝ) * (m : ℝ)) *
          (Real.log (w i : ℝ) + Real.log (m : ℝ) - 1)) =
        (m : ℝ) * (∑ i, (w i : ℝ) * Real.log (w i : ℝ)) +
          (m : ℝ) * Real.log (m : ℝ) * (W : ℝ) -
          (m : ℝ) * (W : ℝ) := by
    calc
      (∑ i, ((w i : ℝ) * (m : ℝ)) *
          (Real.log (w i : ℝ) + Real.log (m : ℝ) - 1)) =
          ∑ i, ((m : ℝ) * ((w i : ℝ) * Real.log (w i : ℝ)) +
            ((m : ℝ) * Real.log (m : ℝ)) * (w i : ℝ) -
            (m : ℝ) * (w i : ℝ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (m : ℝ) * (∑ i, (w i : ℝ) * Real.log (w i : ℝ)) +
          (m : ℝ) * Real.log (m : ℝ) * (W : ℝ) -
          (m : ℝ) * (W : ℝ) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
            rw [← Nat.cast_sum]
  rw [hsum]
  unfold entropyWeight
  dsimp only
  simp only [W]
  ring

theorem multinomial_entropy_polynomial_lower
    {R : Type*} [Fintype R] (w : R → ℕ)
    (m : ℕ) (hm : 0 < m) (hW : 0 < ∑ i, w i) :
    Real.exp ((m : ℝ) * entropyWeight w) ≤
      (6 * (((∑ i, w i) * m + 1 : ℕ) : ℝ)) ^ Fintype.card R *
        (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) := by
  classical
  let W : ℕ := ∑ i, w i
  let N : ℕ := W * m
  let P : ℝ :=
    ∏ i, (((w i * m : ℕ) : ℝ) / Real.exp 1) ^ (w i * m)
  let Q : ℝ := ∏ i, ((w i * m).factorial : ℝ)
  let D : ℝ := (6 * (((N + 1 : ℕ) : ℝ))) ^ Fintype.card R
  let V : ℝ := Nat.multinomial Finset.univ (fun i ↦ w i * m)
  have hwiW (i : R) : w i ≤ W := by
    dsimp [W]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have hlocal (i : R) :
      ((w i * m).factorial : ℝ) ≤
        6 * (((N + 1 : ℕ) : ℝ)) *
          ((((w i * m : ℕ) : ℝ) / Real.exp 1) ^ (w i * m)) := by
    calc
      ((w i * m).factorial : ℝ) ≤
          6 * (((w i * m + 1 : ℕ) : ℝ)) *
            ((((w i * m : ℕ) : ℝ) / Real.exp 1) ^ (w i * m)) :=
        factorial_upper_coarse (w i * m)
      _ ≤ 6 * (((N + 1 : ℕ) : ℝ)) *
            ((((w i * m : ℕ) : ℝ) / Real.exp 1) ^ (w i * m)) := by
        gcongr
        have hmul : w i * m ≤ N := by
          dsimp [N]
          exact Nat.mul_le_mul_right m (hwiW i)
        exact_mod_cast hmul
  have hQ : Q ≤ D * P := by
    calc
      Q ≤ ∏ i, (6 * (((N + 1 : ℕ) : ℝ)) *
          ((((w i * m : ℕ) : ℝ) / Real.exp 1) ^ (w i * m))) := by
            dsimp [Q]
            exact Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun i _ ↦ hlocal i)
      _ = D * P := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        simp only [Finset.card_univ]
        rfl
  have hsumCounts : ∑ i, w i * m = N := by
    rw [← Finset.sum_mul]
  have hspec : Q * V = (N.factorial : ℝ) := by
    have hspecNat := Nat.multinomial_spec Finset.univ (fun i ↦ w i * m)
    dsimp [Q, V]
    rw [← Nat.cast_prod, ← Nat.cast_mul]
    exact_mod_cast (by simpa only [hsumCounts] using hspecNat)
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos fun i _ ↦ by positivity
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity
  have hE0 : 0 ≤ Real.exp ((m : ℝ) * entropyWeight w) := (Real.exp_pos _).le
  have hcancel :
      Real.exp ((m : ℝ) * entropyWeight w) * P =
        (((N : ℕ) : ℝ) / Real.exp 1) ^ N := by
    dsimp [P, N, W]
    exact entropy_cancel w m hm hW
  have hmain :
      Real.exp ((m : ℝ) * entropyWeight w) * Q ≤
        D * (N.factorial : ℝ) := by
    calc
      Real.exp ((m : ℝ) * entropyWeight w) * Q ≤
          Real.exp ((m : ℝ) * entropyWeight w) * (D * P) := by
            gcongr
      _ = D * (Real.exp ((m : ℝ) * entropyWeight w) * P) := by ring
      _ = D * ((((N : ℕ) : ℝ) / Real.exp 1) ^ N) := by rw [hcancel]
      _ ≤ D * (N.factorial : ℝ) := by
        gcongr
        exact factorial_lower_coarse N
  change Real.exp ((m : ℝ) * entropyWeight w) ≤ D * V
  apply le_of_mul_le_mul_right _ hQpos
  calc
    Real.exp ((m : ℝ) * entropyWeight w) * Q ≤
        D * (N.factorial : ℝ) := hmain
    _ = (D * V) * Q := by rw [← hspec]; ring

end MME.DWZMultinomialEntropy

open MME.DWZMultinomialEntropy

/-- A rational histogram's exact multinomial count has its Shannon-entropy
exponential rate, with only a fixed-degree polynomial loss. -/
theorem solution
    {R : Type*} [Fintype R] (w : R → ℕ)
    (m : ℕ) (hm : 0 < m) (hW : 0 < ∑ i, w i) :
    Real.exp
        ((m : ℝ) * (((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (fun i ↦ (w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)))) ≤
      (6 * (((∑ i, w i) * m + 1 : ℕ) : ℝ)) ^ Fintype.card R *
        (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) := by
  rw [← entropyWeight_eq_bits w hW]
  exact multinomial_entropy_polynomial_lower w m hm hW
