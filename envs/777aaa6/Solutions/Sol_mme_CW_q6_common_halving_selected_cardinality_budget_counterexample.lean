-- Prove2me | solution 1 for mme_CW_q6_common_halving_selected_cardinality_budget_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T02:10:17.54537+00:00
-- url     : https://prove2.me/submissions/4ace318f-0c9f-409c-822d-e5d81a3038c7

import Theorems.Thm_mme_CW_q6_binomial_grid_family_selection_bound
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

private theorem two_pow_le_central_binom (n : ℕ) : 2 ^ n ≤ n.centralBinom := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs : 2 * n.centralBinom ≤ (n + 1).centralBinom := by
        apply Nat.le_of_mul_le_mul_left (c := n + 1) _ (by omega)
        rw [Nat.succ_mul_centralBinom_succ]
        nlinarith [Nat.zero_le (n * n.centralBinom)]
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
        _ ≤ 2 * n.centralBinom := Nat.mul_le_mul_left _ ih
        _ ≤ (n + 1).centralBinom := hs

/-- An explicit, deliberately loose threshold suffices: central binomial
mass exceeds the square-root exponential loss. -/
theorem mme_binomial_grid_exceeds_common_halving_loss
    (n : ℕ) (hn : 1000000 ≤ n) :
    Real.exp (200 * Real.sqrt (2 * (n : ℝ) + 1)) < ((2 * n).choose n : ℝ) := by
  have hnR : (1000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot : Real.sqrt (2 * (n : ℝ) + 1) ≤ (n : ℝ) / 400 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hp : 0 ≤ ((n : ℝ) - 1000000) * (n : ℝ) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
  have hhalf : Real.exp (1 / 2 : ℝ) < 2 := by
    rw [Real.exp_half]
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mpr
    have h := Real.exp_one_lt_three
    linarith
  calc
    Real.exp (200 * Real.sqrt (2 * (n : ℝ) + 1)) ≤ Real.exp ((n : ℝ) * (1 / 2)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = Real.exp (1 / 2 : ℝ) ^ n := Real.exp_nat_mul _ _
    _ < (2 : ℝ) ^ n := pow_lt_pow_left₀ hhalf (Real.exp_nonneg _) (by omega)
    _ ≤ ((2 * n).choose n : ℝ) := by
      exact_mod_cast two_pow_le_central_binom n


open MME

/-- Complete balanced grids refute a universal diagonal-selection budget,
even under the original upper bound on the fiber size. -/
theorem solution
    (n : ℕ) (hn : 1000000 ≤ n) :
    ∃ H : ℕ, H ≤ 4 ^ (2 * n) ∧
      ∃ family : CWQ6PrimaryHashFamily (2 * n) 0 (2 * n) 1 H,
        ∃ halving : family.CommonBalancedXYHalving,
          ∀ (q : ℕ) (index : Fin q → Fin 1 × Fin H),
            (∀ i j k, family.PairedCyclicSupported halving (index i) (index j) (index k) →
              i = j ∧ j = k) →
            (q : ℝ) ^ 3 < (H : ℝ) ^ 2 *
              Real.exp (-200 * Real.sqrt (((2 * n + 1 : ℕ) : ℝ))) := by
  obtain ⟨family, halving, hbound⟩ := mme_CW_q6_binomial_grid_family_selection_bound n
  let B := (2 * n).choose n
  have hBnat : 0 < B := Nat.choose_pos (by omega)
  have hB : (0 : ℝ) < B := by exact_mod_cast hBnat
  have hupper : B * B ≤ 4 ^ (2 * n) := by
    calc
      B * B ≤ 2 ^ (2 * n) * 2 ^ (2 * n) :=
        Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
      _ = 4 ^ (2 * n) := by rw [← mul_pow]; norm_num
  refine ⟨B * B, hupper, family, halving, ?_⟩
  intro q index hselected
  have hq : (q : ℝ) ≤ B := by exact_mod_cast hbound q index hselected
  let loss := 200 * Real.sqrt (2 * (n : ℝ) + 1)
  have hexp : Real.exp loss < (B : ℝ) := mme_binomial_grid_exceeds_common_halving_loss n hn
  have hone : (1 : ℝ) < (B : ℝ) * Real.exp (-loss) := by
    have h := mul_lt_mul_of_pos_right hexp (Real.exp_pos (-loss))
    simpa only [← Real.exp_add, add_neg_cancel, Real.exp_zero] using h
  have hcube : (B : ℝ) ^ 3 < ((B : ℝ) * B) ^ 2 * Real.exp (-loss) := by
    have h := mul_lt_mul_of_pos_left hone (pow_pos hB 3)
    convert h using 1 <;> ring
  have hqcube : (q : ℝ) ^ 3 ≤ (B : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hq 3
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, loss, neg_mul] using
    hqcube.trans_lt hcube

