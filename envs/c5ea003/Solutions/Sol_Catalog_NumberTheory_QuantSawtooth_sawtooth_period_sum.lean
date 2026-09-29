-- Prove2me | solution 1 for Catalog.NumberTheory.QuantSawtooth.sawtooth_period_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:00:41.414527+00:00
-- url     : https://prove2.me/submissions/af7d935d-dedb-4e71-afae-907589f9f63a

import Mathlib
import Definitions.Def_NumberTheory_QuantSawtoothBias
open Catalog.NumberTheory.QuantSawtooth Finset in
theorem solution (q : ℕ) (hq : 0 < q) :
    ∑ j ∈ Finset.range q, sawtooth ((j : ℝ) / q) = ((q / 2 : ℕ) : ℝ) - ((q : ℝ) - 1) / 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- on `[0, 1)` the nearest integer to `j/q` is `1` exactly when `2j ≥ q`
  have hround : ∀ j ∈ range q, ((round ((j : ℝ) / q) : ℤ) : ℝ) = if q ≤ 2 * j then 1 else 0 := by
    intro j hj
    rw [mem_range] at hj
    have hjq : (j : ℝ) / q < 1 := (div_lt_one hqR).mpr (by exact_mod_cast hj)
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / q := by positivity
    rw [round_eq]
    split_ifs with h
    · have hh : (1 : ℝ) / 2 ≤ (j : ℝ) / q := by
        rw [div_le_div_iff₀ (by norm_num) hqR]
        have : (q : ℝ) ≤ 2 * j := by exact_mod_cast h
        linarith
      have : Int.floor ((j : ℝ) / q + 1 / 2) = 1 := by
        rw [Int.floor_eq_iff]
        constructor
        · push_cast; linarith
        · push_cast; linarith
      rw [this]
      simp
    · have hh : (j : ℝ) / q < 1 / 2 := by
        rw [div_lt_div_iff₀ hqR (by norm_num)]
        have : (2 * j : ℝ) < q := by exact_mod_cast (by omega : 2 * j < q)
        linarith
      have : Int.floor ((j : ℝ) / q + 1 / 2) = 0 := by
        rw [Int.floor_eq_iff]
        constructor
        · push_cast; linarith
        · push_cast; linarith
      rw [this]
      simp
  -- the count of `j < q` with `2j ≥ q` is `⌊q/2⌋`
  have hcount : ((range q).filter (fun j => q ≤ 2 * j)).card = q / 2 := by
    have : (range q).filter (fun j => q ≤ 2 * j) = Ico ((q + 1) / 2) q := by
      ext j
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    rw [this, Nat.card_Ico]
    omega
  -- Gauss: `Σ_{j<q} j = q(q-1)/2`
  have hgauss : (∑ j ∈ range q, (j : ℝ)) * 2 = (q : ℝ) * ((q : ℝ) - 1) := by
    have h := Finset.sum_range_id_mul_two q
    have h' : ((∑ i ∈ range q, i : ℕ) : ℝ) * 2 = ((q * (q - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast [Nat.cast_sub hq] at h'
    linarith
  unfold sawtooth
  rw [sum_sub_distrib, sum_congr rfl hround, sum_boole, hcount, ← sum_div]
  field_simp
  linarith
