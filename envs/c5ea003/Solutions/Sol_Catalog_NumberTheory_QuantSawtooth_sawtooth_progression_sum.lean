-- Prove2me | solution 1 for Catalog.NumberTheory.QuantSawtooth.sawtooth_progression_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T07:11:02.961792+00:00
-- url     : https://prove2.me/submissions/1371b649-c0c5-470e-9567-71fe78c42cf1

import Mathlib
import Definitions.Def_NumberTheory_QuantSawtoothBias
open Catalog.NumberTheory.QuantSawtooth Finset in
theorem solution {p q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime p q) :
    ∑ k ∈ Finset.range q, sawtooth ((k * p : ℕ) / (q : ℝ))
      = ((q / 2 : ℕ) : ℝ) - ((q : ℝ) - 1) / 2 := by
  -- the full-period sum `Σ_{j<q} sawtooth(j/q)`
  have hbase : ∑ j ∈ Finset.range q, sawtooth ((j : ℝ) / q)
      = ((q / 2 : ℕ) : ℝ) - ((q : ℝ) - 1) / 2 := by
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
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- `sawtooth` is `1`-periodic, so only `k p mod q` matters
  have hper : ∀ k : ℕ, sawtooth ((k * p : ℕ) / (q : ℝ)) = sawtooth (((k * p % q : ℕ) : ℝ) / q) := by
    intro k
    have hdec : ((k * p : ℕ) : ℝ) / q = ((k * p % q : ℕ) : ℝ) / q + ((k * p / q : ℕ) : ℝ) := by
      have h := Nat.mod_add_div (k * p) q
      have h' : ((k * p : ℕ) : ℝ) = ((k * p % q : ℕ) : ℝ) + q * ((k * p / q : ℕ) : ℝ) := by
        exact_mod_cast h.symm
      rw [h']
      field_simp
    unfold sawtooth
    rw [hdec, round_add_natCast, Int.cast_add, Int.cast_natCast]
    ring
  -- `k ↦ k p mod q` permutes `{0, …, q-1}` since `p` is invertible mod `q`
  have hinj : Set.InjOn (fun k => k * p % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have hmod : a * p ≡ b * p [MOD q] := hab
    have := Nat.ModEq.cancel_right_of_coprime (by rw [Nat.gcd_comm]; exact hcop) hmod
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have himage : (Finset.range q).image (fun k => k * p % q) = Finset.range q := by
    apply eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨k, -, rfl⟩ := mem_image.mp hj
      exact mem_range.mpr (Nat.mod_lt _ hq)
    · rw [card_image_of_injOn hinj]
  calc ∑ k ∈ Finset.range q, sawtooth ((k * p : ℕ) / (q : ℝ))
      = ∑ k ∈ Finset.range q, sawtooth (((k * p % q : ℕ) : ℝ) / q) := sum_congr rfl (fun k _ => hper k)
    _ = ∑ j ∈ (Finset.range q).image (fun k => k * p % q), sawtooth ((j : ℝ) / q) :=
        (sum_image (f := fun j : ℕ => sawtooth ((j : ℝ) / q)) (fun a ha b hb h => hinj ha hb h)).symm
    _ = ∑ j ∈ Finset.range q, sawtooth ((j : ℝ) / q) := by rw [himage]
    _ = ((q / 2 : ℕ) : ℝ) - ((q : ℝ) - 1) / 2 := hbase
