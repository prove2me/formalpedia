-- Prove2me | solution 1 for Catalog.NumberTheory.QuantTuran.sawtooth_l1_period
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:06:51.520985+00:00
-- url     : https://prove2.me/submissions/e80710eb-9d83-45d5-bf31-fc99b61193e4

import Mathlib
import Definitions.Def_NumberTheory_QuantL1TuranBridge
open Catalog.NumberTheory.QuantTuran Finset in
theorem solution {q : ℕ} (hq : 0 < q) :
    ∑ j ∈ Finset.range q, |sawtooth ((j : ℝ) / q)|
      = ((q : ℝ) ^ 2 - (q % 2 : ℕ)) / (4 * q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set c := (q + 1) / 2 with hc
  have hcq : c ≤ q := by omega
  -- |round(x) - x| on `[0,1)`: `x` below one half, `1 - x` from one half on
  have hterm : ∀ j < q, |sawtooth ((j : ℝ) / q)| = if 2 * j < q then (j : ℝ) / q else 1 - (j : ℝ) / q := by
    intro j hj
    have hjq : (j : ℝ) / q < 1 := (div_lt_one hqR).mpr (by exact_mod_cast hj)
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / q := by positivity
    unfold sawtooth
    rw [round_eq]
    split_ifs with h
    · have hh : (j : ℝ) / q < 1 / 2 := by
        rw [div_lt_div_iff₀ hqR (by norm_num)]
        have : (2 * j : ℝ) < q := by exact_mod_cast h
        linarith
      have : Int.floor ((j : ℝ) / q + 1 / 2) = 0 := by
        rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      rw [this]
      simp only [Int.cast_zero, zero_sub, abs_neg]
      exact abs_of_nonneg hj0
    · have hh : (1 : ℝ) / 2 ≤ (j : ℝ) / q := by
        rw [div_le_div_iff₀ (by norm_num) hqR]
        have : (q : ℝ) ≤ 2 * j := by exact_mod_cast (by omega : q ≤ 2 * j)
        linarith
      have : Int.floor ((j : ℝ) / q + 1 / 2) = 1 := by
        rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      rw [this]
      simp only [Int.cast_one]
      exact abs_of_nonneg (by linarith)
  -- Gauss sums
  have hG : ∀ n : ℕ, (∑ j ∈ range n, (j : ℝ)) * 2 = n * ((n : ℝ) - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ]; push_cast; linarith
  -- split `range q` at `c`
  have hsplit := sum_range_add_sum_Ico (fun j => |sawtooth ((j : ℝ) / q)|) hcq
  have hlow : ∑ j ∈ range c, |sawtooth ((j : ℝ) / q)| = (∑ j ∈ range c, (j : ℝ)) / q := by
    rw [sum_div]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [hterm j (by omega), if_pos (by omega)]
  have hhigh : ∑ j ∈ Ico c q, |sawtooth ((j : ℝ) / q)|
      = ((q : ℝ) - c) - (∑ j ∈ Ico c q, (j : ℝ)) / q := by
    have : ∑ j ∈ Ico c q, |sawtooth ((j : ℝ) / q)| = ∑ j ∈ Ico c q, (1 - (j : ℝ) / q) := by
      refine sum_congr rfl fun j hj => ?_
      rw [mem_Ico] at hj
      rw [hterm j hj.2, if_neg (by omega)]
    rw [this, sum_sub_distrib, sum_const, Nat.card_Ico, nsmul_one, sum_div, Nat.cast_sub hcq]
  have hIco := sum_range_add_sum_Ico (fun j => (j : ℝ)) hcq
  have hGq := hG q
  have hGc := hG c
  rw [← hsplit, hlow, hhigh]
  -- parity cases for the closed form
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' q
  · have hcm : c = m := by omega
    have hmod : 2 * m % 2 = 0 := by omega
    rw [hmod]
    rw [hcm] at hGc hIco ⊢
    push_cast at hGq hIco ⊢
    have hm0 : (m : ℝ) ≠ 0 := by
      have : 0 < m := by omega
      positivity
    have hA : ∑ j ∈ range m, (j : ℝ) = m * (m - 1) / 2 := by linarith
    have hB : ∑ j ∈ Ico m (2 * m), (j : ℝ) = 2 * m * (2 * m - 1) / 2 - m * (m - 1) / 2 := by
      linarith
    rw [hA, hB]
    field_simp
    ring
  · have hcm : c = m + 1 := by omega
    have hmod : (2 * m + 1) % 2 = 1 := by omega
    rw [hmod]
    rw [hcm] at hGc hIco ⊢
    push_cast at hGq hGc hIco ⊢
    have hq0 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    have hA : ∑ j ∈ range (m + 1), (j : ℝ) = (m + 1) * m / 2 := by linarith
    have hB : ∑ j ∈ Ico (m + 1) (2 * m + 1), (j : ℝ)
        = (2 * m + 1) * (2 * m) / 2 - (m + 1) * m / 2 := by
      linarith
    rw [hA, hB]
    field_simp
    ring
