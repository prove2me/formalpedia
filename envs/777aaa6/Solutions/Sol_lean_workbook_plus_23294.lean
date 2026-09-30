-- Prove2me | solution 1 for lean_workbook_plus_23294
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:53:34.760674+00:00
-- url     : https://prove2.me/submissions/1c946093-0940-43d8-b36f-1dbe99a4cac2

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open Filter Finset
open scoped Topology

noncomputable def radicalHarmonicTerm (x : ℝ) : ℝ :=
  (1 + x + x ^ 2) / Real.sqrt (1 + x ^ 2 + x ^ 6)

theorem radicalHarmonicTerm_pos {x : ℝ} (hx : 0 ≤ x) : 0 < radicalHarmonicTerm x := by
  unfold radicalHarmonicTerm
  positivity

theorem radicalHarmonicTerm_lower {x : ℝ} (hx : 1 ≤ x) :
    1 / (2 * x) ≤ radicalHarmonicTerm x := by
  have hpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h₂₆ : x ^ 2 ≤ x ^ 6 := pow_le_pow_right₀ hx (by decide)
  have h₀₆ : 1 ≤ x ^ 6 := one_le_pow₀ hx
  have hd : Real.sqrt (1 + x ^ 2 + x ^ 6) ≤ 2 * x ^ 3 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [pow_nonneg hpos.le 6]
  unfold radicalHarmonicTerm
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg x]

theorem radicalHarmonicTerm_normalized {x : ℝ} (hx : 0 < x) :
    x * radicalHarmonicTerm x =
      (1 / x ^ 2 + 1 / x + 1) / Real.sqrt (1 / x ^ 6 + 1 / x ^ 4 + 1) := by
  have heq : 1 + x ^ 2 + x ^ 6 =
      (x ^ 3) ^ 2 * (1 / x ^ 6 + 1 / x ^ 4 + 1) := by
    field_simp
  have hs : Real.sqrt (1 + x ^ 2 + x ^ 6) =
      x ^ 3 * Real.sqrt (1 / x ^ 6 + 1 / x ^ 4 + 1) := by
    rw [heq, Real.sqrt_mul (sq_nonneg (x ^ 3)), Real.sqrt_sq (pow_nonneg hx.le 3)]
  have ht : Real.sqrt (1 / x ^ 6 + 1 / x ^ 4 + 1) ≠ 0 := by positivity
  unfold radicalHarmonicTerm
  rw [hs]
  field_simp

theorem radicalHarmonicTerm_scaled_limit :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) * radicalHarmonicTerm (n + 2)) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_add_atTop_iff_nat 2).mpr (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hA : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2 + 1 / ((n : ℝ) + 2) + 1)
      atTop (𝓝 1) := by
    simpa only [div_pow, one_pow, zero_pow (by decide : 2 ≠ 0), zero_add] using
      ((hi.pow 2).add hi).add_const 1
  have hB : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 6 + 1 / ((n : ℝ) + 2) ^ 4 + 1)
      atTop (𝓝 1) := by
    simpa only [div_pow, one_pow, zero_pow (by decide : 6 ≠ 0),
      zero_pow (by decide : 4 ≠ 0), zero_add] using
      ((hi.pow 6).add (hi.pow 4)).add_const 1
  have hS : Tendsto (fun n : ℕ => Real.sqrt
      (1 / ((n : ℝ) + 2) ^ 6 + 1 / ((n : ℝ) + 2) ^ 4 + 1)) atTop (𝓝 1) := by
    simpa only [Real.sqrt_one] using Real.continuous_sqrt.continuousAt.tendsto.comp hB
  have h := hA.div hS (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards with n
  exact (radicalHarmonicTerm_normalized (by positivity : 0 < (n : ℝ) + 2)).symm

theorem radicalHarmonicTerm_tendsto_zero :
    Tendsto (fun n : ℕ => radicalHarmonicTerm (n + 2)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_add_atTop_iff_nat 2).mpr (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := radicalHarmonicTerm_scaled_limit.mul hi
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards with n
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

theorem radicalHarmonicTerm_not_summable :
    ¬ Summable (fun n : ℕ => radicalHarmonicTerm (n + 2)) := by
  intro hs
  have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2)) := by
    apply (hs.mul_left 2).of_nonneg_of_le (fun n => by positivity)
    intro n
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    calc
      1 / ((n : ℝ) + 2) = 2 * (1 / (2 * ((n : ℝ) + 2))) := by field_simp
      _ ≤ 2 * radicalHarmonicTerm (n + 2) :=
        mul_le_mul_of_nonneg_left
          (radicalHarmonicTerm_lower (by nlinarith [Nat.cast_nonneg (α := ℝ) n])) (by norm_num)
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 2).mp
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hh

theorem radicalHarmonicTerm_sums_diverge :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, radicalHarmonicTerm (n + 2)) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => (radicalHarmonicTerm_pos (by positivity : 0 ≤ (n : ℝ) + 2)).le)]
  exact radicalHarmonicTerm_not_summable

theorem radicalHarmonicTerm_absolute_sums_diverge :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, |radicalHarmonicTerm (n + 2)|) atTop atTop := by
  convert radicalHarmonicTerm_sums_diverge using 1
  ext N
  apply Finset.sum_congr rfl
  intro n hn
  exact abs_of_pos (radicalHarmonicTerm_pos (by positivity : 0 ≤ (n : ℝ) + 2))

theorem solution (n : ℕ) (hn : 2 ≤ n) (a_n : ℝ)
    (ha_n : a_n = (1 + n + n ^ 2) / Real.sqrt (1 + n ^ 2 + n ^ 6)) :
    ∃ l, ∑' n : ℕ, a_n = l := by
  exact ⟨∑' n : ℕ, a_n, rfl⟩

#print axioms radicalHarmonicTerm
#print axioms radicalHarmonicTerm_pos
#print axioms radicalHarmonicTerm_lower
#print axioms radicalHarmonicTerm_normalized
#print axioms radicalHarmonicTerm_scaled_limit
#print axioms radicalHarmonicTerm_tendsto_zero
#print axioms radicalHarmonicTerm_not_summable
#print axioms radicalHarmonicTerm_sums_diverge
#print axioms radicalHarmonicTerm_absolute_sums_diverge
#print axioms solution
