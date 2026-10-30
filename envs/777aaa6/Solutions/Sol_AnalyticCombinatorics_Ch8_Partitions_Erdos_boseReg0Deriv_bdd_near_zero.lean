-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.boseReg0Deriv_bdd_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:18:34.642482+00:00
-- url     : https://prove2.me/submissions/2d1b7377-917d-42c7-92a5-8395f74465db

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateDeriv
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# Mass-rate campaign: polynomial exponential bounds (R10 bricks 1–3)

Two-sided polynomial bounds for `e^x − 1` on `[0,1]` from `Real.exp_bound` at orders 3, 4 —
the only exp-Taylor input the whole moment package needs.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Order-4 remainder: `|e^x − 1 − x − x²/2 − x³/6| ≤ x⁴` on `[0,1]`. -/
lemma exp_sub_one_order4_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6| ≤ x ^ 4 := by
  have habs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    exact hx1
  have h := Real.exp_bound habs (n := 4) (by norm_num)
  have hsum : ∑ i ∈ Finset.range 4, x ^ i / (Nat.factorial i : ℝ)
      = 1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
  rw [hsum] at h
  have habs4 : |x| ^ 4 = x ^ 4 := by
    rw [abs_of_nonneg hx0]
  rw [habs4] at h
  calc |Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6|
      = |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)| := by ring_nf
    _ ≤ x ^ 4 * ((4 : ℕ).succ / ((Nat.factorial 4 : ℝ) * 4)) := h
    _ ≤ x ^ 4 := by
        have hx4 : (0 : ℝ) ≤ x ^ 4 := by positivity
        have hc : ((4 : ℕ).succ : ℝ) / ((Nat.factorial 4 : ℝ) * 4) ≤ 1 := by
          norm_num [Nat.factorial]
        nlinarith [hx4, hc]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Mass-rate campaign: near-zero derivative bound (R10 brick 16)

`|boseReg0′| ≤ 32` on `(0,1]`, via the hand-computed degree-6 cancellation: with
`y = eˣ−1 = P + δ`, `P = x + x²/2 + x³/6`, `|δ| ≤ x⁴`,

  `2y³ − x³(2+3y+y²) = (−x⁶/4 − x⁷/6 − x⁸/12 − x⁹/54)
      + δ(6x² + 3x³ + 3x⁴/2 − x⁶/6) + δ²(6P − x³) + 2δ³`

(a `ring`-checkable identity), each piece `≤ 11x⁶` in absolute value, denominator
`x³y³ ≥ x⁶`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Rational form of the derivative. -/
lemma boseReg0Deriv_eq_small_num {x : ℝ} (hx : 0 < x) :
    boseReg0Deriv x
      = (2 * (Real.exp x - 1) ^ 3 - x ^ 3 * Real.exp x * (Real.exp x + 1)) /
          (x ^ 3 * (Real.exp x - 1) ^ 3) := by
  have hy : 0 < Real.exp x - 1 := by
    have := Real.add_one_lt_exp (x := x) hx.ne'
    linarith
  rw [boseReg0Deriv]
  field_simp
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 1000000
theorem solution {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |boseReg0Deriv x| ≤ 32 := by
  set y : ℝ := Real.exp x - 1 with hydef
  have hyx : x ≤ y := by
    rw [hydef]
    linarith [Real.add_one_le_exp x]
  have hypos : 0 < y := lt_of_lt_of_le hx0 hyx
  set δ : ℝ := y - (x + x ^ 2 / 2 + x ^ 3 / 6) with hδdef
  have hδ : |δ| ≤ x ^ 4 := by
    rw [hδdef, hydef]
    have := exp_sub_one_order4_bound hx0.le hx1
    convert this using 2
    ring
  have hδhi := (abs_le.mp hδ).2
  have hδlo := (abs_le.mp hδ).1
  -- the hand-computed decomposition (pure ring identity)
  have hkey : 2 * y ^ 3 - x ^ 3 * (2 + 3 * y + y ^ 2)
      = (-(x ^ 6 / 4) - x ^ 7 / 6 - x ^ 8 / 12 - x ^ 9 / 54)
        + δ * (6 * x ^ 2 + 3 * x ^ 3 + 3 * x ^ 4 / 2 - x ^ 6 / 6)
        + δ ^ 2 * (6 * (x + x ^ 2 / 2 + x ^ 3 / 6) - x ^ 3)
        + 2 * δ ^ 3 := by
    have hy_eq : y = (x + x ^ 2 / 2 + x ^ 3 / 6) + δ := by
      rw [hδdef]
      ring
    rw [hy_eq]
    ring
  -- piecewise bounds on (0,1]
  have hxpow : ∀ k l : ℕ, k ≤ l → x ^ l ≤ x ^ k := by
    intro k l hkl
    exact pow_le_pow_of_le_one hx0.le hx1 hkl
  have hQ2pos : (0 : ℝ) ≤ 6 * x ^ 2 + 3 * x ^ 3 + 3 * x ^ 4 / 2 - x ^ 6 / 6 := by
    have h62 := hxpow 2 6 (by norm_num)
    nlinarith [pow_pos hx0 2, pow_pos hx0 3, pow_pos hx0 4]
  have hQ2le : 6 * x ^ 2 + 3 * x ^ 3 + 3 * x ^ 4 / 2 - x ^ 6 / 6 ≤ 11 * x ^ 2 := by
    have h32 := hxpow 2 3 (by norm_num)
    have h42 := hxpow 2 4 (by norm_num)
    nlinarith [pow_pos hx0 6]
  have hQ3pos : (0 : ℝ) ≤ 6 * (x + x ^ 2 / 2 + x ^ 3 / 6) - x ^ 3 := by
    nlinarith [hx0.le, pow_pos hx0 2, pow_pos hx0 3]
  have hQ3le : 6 * (x + x ^ 2 / 2 + x ^ 3 / 6) - x ^ 3 ≤ 11 * x := by
    have h21 := hxpow 1 2 (by norm_num)
    have h31 := hxpow 1 3 (by norm_num)
    nlinarith
  -- |δ·Q₂| ≤ 11x⁶
  have hp2 : |δ * (6 * x ^ 2 + 3 * x ^ 3 + 3 * x ^ 4 / 2 - x ^ 6 / 6)| ≤ 11 * x ^ 6 := by
    rw [abs_mul, abs_of_nonneg hQ2pos]
    calc |δ| * (6 * x ^ 2 + 3 * x ^ 3 + 3 * x ^ 4 / 2 - x ^ 6 / 6)
        ≤ x ^ 4 * (11 * x ^ 2) := by
          apply mul_le_mul hδ hQ2le hQ2pos (by positivity)
      _ = 11 * x ^ 6 := by ring
  -- |δ²·Q₃| ≤ 11x⁶ (using x⁹ ≤ x⁶)
  have hp3 : |δ ^ 2 * (6 * (x + x ^ 2 / 2 + x ^ 3 / 6) - x ^ 3)| ≤ 11 * x ^ 6 := by
    rw [abs_mul, abs_of_nonneg hQ3pos]
    have hδsq : δ ^ 2 ≤ x ^ 8 := by nlinarith [hδhi, hδlo]
    have habs_sq : |δ ^ 2| = δ ^ 2 := abs_of_nonneg (sq_nonneg δ)
    rw [habs_sq]
    calc δ ^ 2 * (6 * (x + x ^ 2 / 2 + x ^ 3 / 6) - x ^ 3)
        ≤ x ^ 8 * (11 * x) := by
          apply mul_le_mul hδsq hQ3le hQ3pos (by positivity)
      _ = 11 * x ^ 9 := by ring
      _ ≤ 11 * x ^ 6 := by
          have := hxpow 6 9 (by norm_num)
          linarith
  -- |2δ³| ≤ 2x⁶
  have hp4 : |2 * δ ^ 3| ≤ 2 * x ^ 6 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h1 : |δ ^ 3| = |δ| ^ 3 := by
      rw [abs_pow]
    rw [h1]
    have h2 : |δ| ^ 3 ≤ (x ^ 4) ^ 3 := pow_le_pow_left₀ (abs_nonneg δ) hδ 3
    have h3 : (x ^ 4) ^ 3 = x ^ 12 := by ring
    have h4 := hxpow 6 12 (by norm_num)
    nlinarith [h2]
  -- |B| ≤ x⁶
  have hpB : |(-(x ^ 6 / 4) - x ^ 7 / 6 - x ^ 8 / 12 - x ^ 9 / 54)| ≤ x ^ 6 := by
    have h76 := hxpow 6 7 (by norm_num)
    have h86 := hxpow 6 8 (by norm_num)
    have h96 := hxpow 6 9 (by norm_num)
    rw [abs_le]
    constructor
    · nlinarith [pow_pos hx0 6]
    · nlinarith [pow_pos hx0 6, pow_pos hx0 7, pow_pos hx0 8, pow_pos hx0 9]
  -- total numerator bound: ≤ 25x⁶ ≤ 32x⁶... use 32 for slack
  have hnum_abs : |2 * y ^ 3 - x ^ 3 * (2 + 3 * y + y ^ 2)| ≤ 32 * x ^ 6 := by
    rw [hkey]
    have t1 := abs_add_le ((-(x ^ 6 / 4) - x ^ 7 / 6 - x ^ 8 / 12 - x ^ 9 / 54)
      + δ * (6 * x ^ 2 + 3 * x ^ 3 + 3 * x ^ 4 / 2 - x ^ 6 / 6)
      + δ ^ 2 * (6 * (x + x ^ 2 / 2 + x ^ 3 / 6) - x ^ 3)) (2 * δ ^ 3)
    have t2 := abs_add_le ((-(x ^ 6 / 4) - x ^ 7 / 6 - x ^ 8 / 12 - x ^ 9 / 54)
      + δ * (6 * x ^ 2 + 3 * x ^ 3 + 3 * x ^ 4 / 2 - x ^ 6 / 6))
      (δ ^ 2 * (6 * (x + x ^ 2 / 2 + x ^ 3 / 6) - x ^ 3))
    have t3 := abs_add_le (-(x ^ 6 / 4) - x ^ 7 / 6 - x ^ 8 / 12 - x ^ 9 / 54)
      (δ * (6 * x ^ 2 + 3 * x ^ 3 + 3 * x ^ 4 / 2 - x ^ 6 / 6))
    linarith [hp2, hp3, hp4, hpB, pow_nonneg hx0.le 6]
  -- numerator in exp variables + denominator ≥ x⁶
  have hnum_eq : 2 * (Real.exp x - 1) ^ 3 - x ^ 3 * Real.exp x * (Real.exp x + 1)
      = 2 * y ^ 3 - x ^ 3 * (2 + 3 * y + y ^ 2) := by
    rw [hydef]
    ring
  have hden_ge : x ^ 6 ≤ x ^ 3 * y ^ 3 := by
    have hy3 : x ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hx0.le hyx 3
    nlinarith [pow_pos hx0 3, mul_le_mul_of_nonneg_left hy3 (pow_pos hx0 3).le]
  have hden_pos : 0 < x ^ 3 * y ^ 3 := by positivity
  rw [boseReg0Deriv_eq_small_num hx0]
  rw [show x ^ 3 * (Real.exp x - 1) ^ 3 = x ^ 3 * y ^ 3 by rw [hydef]]
  rw [hnum_eq, abs_div, abs_of_pos hden_pos]
  calc |2 * y ^ 3 - x ^ 3 * (2 + 3 * y + y ^ 2)| / (x ^ 3 * y ^ 3)
      ≤ (32 * x ^ 6) / x ^ 6 :=
        div_le_div₀ (by positivity) hnum_abs (by positivity) hden_ge
    _ = 32 := by
        field_simp
