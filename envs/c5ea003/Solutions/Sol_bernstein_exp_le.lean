-- Prove2me | solution 1 for bernstein_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-24T01:45:05.684371+00:00
-- url     : https://prove2.me/submissions/6b84aa15-838f-4e64-b1bb-95b4790de3f9

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

open Real Set

private lemma factorial_ge (k : ℕ) (hk : 2 ≤ k) : 2 * 3 ^ (k - 2) ≤ (Nat.factorial k) := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · omega
      · simp [Nat.factorial]
    · have ih' := ih hn
      have hstep : (n+1) - 2 = (n - 2) + 1 := by omega
      rw [hstep, pow_succ]
      have hfact : Nat.factorial (n+1) = (n+1) * Nat.factorial n := Nat.factorial_succ n
      rw [hfact]
      have h1 : 2 * (3 ^ (n - 2) * 3) = 3 * (2 * 3 ^ (n - 2)) := by ring
      rw [h1]
      calc 3 * (2 * 3 ^ (n - 2)) ≤ 3 * (Nat.factorial n) := by
              exact Nat.mul_le_mul_left 3 ih'
        _ ≤ (n + 1) * (Nat.factorial n) := by
              apply Nat.mul_le_mul_right
              omega

private lemma term_bound (lam : ℝ) (h0 : 0 ≤ lam) (k : ℕ) (hk : 2 ≤ k) :
    lam ^ k / ((Nat.factorial k : ℝ)) ≤ (lam ^ 2 / 2) * (lam / 3) ^ (k - 2) := by
  have hfact_pos : (0:ℝ) < ((Nat.factorial k : ℝ)) := by exact_mod_cast Nat.factorial_pos k
  have hfact_ge : (2 : ℝ) * 3 ^ (k - 2) ≤ ((Nat.factorial k : ℝ)) := by
    have := factorial_ge k hk
    have : ((2 * 3 ^ (k - 2) : ℕ) : ℝ) ≤ ((Nat.factorial k) : ℝ) := by exact_mod_cast this
    push_cast at this
    convert this using 2
  have hk2 : k = 2 + (k - 2) := by omega
  have hpow : lam ^ k = lam ^ 2 * lam ^ (k - 2) := by
    conv_lhs => rw [hk2]
    rw [pow_add]
  rw [hpow]
  have hlamk2 : (0:ℝ) ≤ lam ^ (k - 2) := by positivity
  have hlam2 : (0:ℝ) ≤ lam ^ 2 := by positivity
  have hrhs : (lam ^ 2 / 2) * (lam / 3) ^ (k - 2)
      = (lam ^ 2 * lam ^ (k - 2)) / (2 * 3 ^ (k - 2)) := by
    rw [div_pow]
    field_simp
  rw [hrhs]
  rw [div_le_div_iff₀ hfact_pos (by positivity)]
  have hnn : (0:ℝ) ≤ lam ^ 2 * lam ^ (k - 2) := by positivity
  apply mul_le_mul_of_nonneg_left hfact_ge hnn

private lemma real_exp_eq_tsum (x : ℝ) : Real.exp x = ∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ) := by
  rw [Real.exp_eq_exp_ℝ]
  rw [NormedSpace.exp_eq_tsum_div]

private lemma real_exp_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := by
  have hsummable : Summable (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) := by
    have : Summable (fun n : ℕ => ‖x ^ n / (Nat.factorial n : ℝ)‖) := by
      simpa [Real.norm_eq_abs, abs_div, abs_pow] using
        (Real.summable_pow_div_factorial |x|)
    exact this.of_norm
  have h := hsummable.hasSum
  rw [real_exp_eq_tsum x]
  exact h

theorem solution (lam : ℝ) (h0 : 0 ≤ lam) (h3 : lam < 3) :
    Real.exp lam - 1 - lam ≤ lam ^ 2 / (2 * (1 - lam / 3)) := by
  have hden : (0:ℝ) < 1 - lam / 3 := by linarith
  have hexp := real_exp_hasSum lam
  have htail : HasSum (fun k : ℕ => lam ^ (k + 2) / (Nat.factorial (k + 2) : ℝ))
      (Real.exp lam - ∑ i ∈ Finset.range 2, lam ^ i / (Nat.factorial i : ℝ)) := by
    have := (hasSum_nat_add_iff' 2).mpr hexp
    simpa using this
  have hsub : ∑ i ∈ Finset.range 2, lam ^ i / (Nat.factorial i : ℝ) = 1 + lam := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsub] at htail
  have htail_eq : Real.exp lam - 1 - lam = ∑' k : ℕ, lam ^ (k + 2) / (Nat.factorial (k + 2) : ℝ) := by
    have h := htail.tsum_eq
    rw [h]; ring
  have hgeo_lt : lam / 3 < 1 := by linarith
  have hgeo_nn : (0:ℝ) ≤ lam / 3 := by positivity
  have hgeo : HasSum (fun k : ℕ => (lam / 3) ^ k) (1 - lam / 3)⁻¹ :=
    hasSum_geometric_of_lt_one hgeo_nn hgeo_lt
  have hmaj : HasSum (fun k : ℕ => (lam ^ 2 / 2) * (lam / 3) ^ k)
      ((lam ^ 2 / 2) * (1 - lam / 3)⁻¹) := hgeo.mul_left _
  have hcompare : ∀ k : ℕ, lam ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)
      ≤ (lam ^ 2 / 2) * (lam / 3) ^ k := by
    intro k
    have hb := term_bound lam h0 (k + 2) (by omega)
    simpa using hb
  have htail_summable : Summable (fun k : ℕ => lam ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)) :=
    htail.summable
  have hmaj_summable : Summable (fun k : ℕ => (lam ^ 2 / 2) * (lam / 3) ^ k) := hmaj.summable
  calc Real.exp lam - 1 - lam
      = ∑' k : ℕ, lam ^ (k + 2) / (Nat.factorial (k + 2) : ℝ) := htail_eq
    _ ≤ ∑' k : ℕ, (lam ^ 2 / 2) * (lam / 3) ^ k :=
        Summable.tsum_le_tsum hcompare htail_summable hmaj_summable
    _ = (lam ^ 2 / 2) * (1 - lam / 3)⁻¹ := hmaj.tsum_eq
    _ = lam ^ 2 / (2 * (1 - lam / 3)) := by
        rw [div_mul_eq_div_div]
        ring_nf
