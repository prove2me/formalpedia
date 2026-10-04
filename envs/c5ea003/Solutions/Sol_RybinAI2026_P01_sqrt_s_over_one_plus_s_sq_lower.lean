-- Prove2me | solution 1 for RybinAI2026.P01.sqrt_s_over_one_plus_s_sq_lower
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T13:14:48.333907+00:00
-- url     : https://prove2.me/submissions/7121fb84-b953-4957-8d3e-04542c78af18

import Mathlib

open Real MeasureTheory intervalIntegral Set

theorem solution :
    (3 / 4 : ℝ) ≤ ∫ t in (0 : ℝ)..4, Real.sqrt t / (1 + t ^ 2) := by
  let f : ℝ → ℝ := fun t => Real.sqrt t / (1 + t ^ 2)
  have hden_pos : ∀ t : ℝ, 0 < 1 + t ^ 2 := fun t => by
    nlinarith [sq_nonneg t]
  have hcont : Continuous f := by
    refine Continuous.div continuous_sqrt ?_ ?_
    · fun_prop
    · intro t
      exact (hden_pos t).ne'
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    fun a b => hcont.continuousOn.intervalIntegrable
  have hint_div (c : ℝ) (hc : c ≠ 0) (a b : ℝ) :
      IntervalIntegrable (fun t => Real.sqrt t / c) volume a b := by
    have hcont' : Continuous fun t : ℝ => Real.sqrt t / c :=
      continuous_sqrt.div continuous_const fun _ => hc
    exact hcont'.continuousOn.intervalIntegrable
  have hle_piece {a b c : ℝ} (hc : 0 < c)
      (hdom : ∀ t ∈ Icc a b, 1 + t ^ 2 ≤ c) :
      ∀ t ∈ Icc a b, Real.sqrt t / c ≤ f t := by
    intro t ht
    have hden : 1 + t ^ 2 ≤ c := hdom t ht
    simpa [f] using
      (div_le_div_of_nonneg_left (sqrt_nonneg t) (hden_pos t) hden)
  have h01 : ∀ t ∈ Icc (0 : ℝ) 1, Real.sqrt t / 2 ≤ f t := by
    refine hle_piece (by norm_num) ?_
    intro t ht
    have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    linarith
  have h12 : ∀ t ∈ Icc (1 : ℝ) 2, Real.sqrt t / 5 ≤ f t := by
    refine hle_piece (by norm_num) ?_
    intro t ht
    have : t ^ 2 ≤ 4 := by nlinarith [ht.1, ht.2]
    linarith
  have h24 : ∀ t ∈ Icc (2 : ℝ) 4, Real.sqrt t / 17 ≤ f t := by
    refine hle_piece (by norm_num) ?_
    intro t ht
    have : t ^ 2 ≤ 16 := by nlinarith [ht.1, ht.2]
    linarith
  have hmono01 :=
    integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1) (by norm_num)
      (hint_div 2 (by norm_num) 0 1) (hint 0 1) h01
  have hmono12 :=
    integral_mono_on (μ := volume) (a := (1 : ℝ)) (b := 2) (by norm_num)
      (hint_div 5 (by norm_num) 1 2) (hint 1 2) h12
  have hmono24 :=
    integral_mono_on (μ := volume) (a := (2 : ℝ)) (b := 4) (by norm_num)
      (hint_div 17 (by norm_num) 2 4) (hint 2 4) h24
  have hadd12 :
      (∫ t in (1 : ℝ)..2, f t) + ∫ t in (2 : ℝ)..4, f t = ∫ t in (1 : ℝ)..4, f t :=
    integral_add_adjacent_intervals (hint 1 2) (hint 2 4)
  have hadd04 :
      (∫ t in (0 : ℝ)..1, f t) + ∫ t in (1 : ℝ)..4, f t = ∫ t in (0 : ℝ)..4, f t :=
    integral_add_adjacent_intervals (hint 0 1) (hint 1 4)
  -- Evaluate the comparison integrals via `x ↦ x^(1/2)`.
  have int_rpow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      ∫ t in a..b, Real.sqrt t = (b ^ (3 / 2 : ℝ) - a ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ) := by
    have hr : -1 < (1 / 2 : ℝ) := by norm_num
    have hcongr :
        ∫ t in a..b, Real.sqrt t = ∫ t in a..b, t ^ (1 / 2 : ℝ) := by
      apply integral_congr
      intro t ht
      rw [sqrt_eq_rpow]
    rw [hcongr]
    convert integral_rpow (a := a) (b := b) (r := (1 / 2 : ℝ)) (Or.inl hr) using 1 <;> norm_num
  have int_div (c a b : ℝ) (hc : c ≠ 0) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      ∫ t in a..b, Real.sqrt t / c =
        (1 / c) * ((b ^ (3 / 2 : ℝ) - a ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ)) := by
    have hcongr :
        ∫ t in a..b, Real.sqrt t / c = ∫ t in a..b, (1 / c) * Real.sqrt t := by
      apply integral_congr
      intro t _
      field_simp
    rw [hcongr, intervalIntegral.integral_const_mul, int_rpow a b ha hb]
  have i01 := int_div 2 0 1 (by norm_num) (by norm_num) (by norm_num)
  have i12 := int_div 5 1 2 (by norm_num) (by norm_num) (by norm_num)
  have i24 := int_div 17 2 4 (by norm_num) (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ^ (3 / 2 : ℝ) = 0 := by
    simpa using (Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0))
  have h1 : (1 : ℝ) ^ (3 / 2 : ℝ) = 1 := by
    simpa using (Real.one_rpow (3 / 2 : ℝ))
  have h2 : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
    have hpos : (0 : ℝ) < 2 := by norm_num
    rw [show (3 / 2 : ℝ) = (1 : ℝ) + 1 / 2 by norm_num, Real.rpow_add hpos]
    rw [Real.rpow_one, ← sqrt_eq_rpow]
  have h4 : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
    have hpos : (0 : ℝ) < 4 := by norm_num
    rw [show (3 / 2 : ℝ) = (1 : ℝ) + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one]
    have hsq : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [← sqrt_eq_rpow]
      norm_num
    rw [hsq]
    norm_num
  -- numerical comparison of the sum of the three lower bounds
  have hsum :
      (1 / 2) * ((1 ^ (3 / 2 : ℝ) - 0 ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ))
        + (1 / 5) * ((2 ^ (3 / 2 : ℝ) - 1 ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ))
        + (1 / 17) * ((4 ^ (3 / 2 : ℝ) - 2 ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ))
        = (131 + 48 * Real.sqrt 2) / 255 := by
    rw [h0, h1, h2, h4]
    ring
  have hnum : (3 / 4 : ℝ) ≤ (131 + 48 * Real.sqrt 2) / 255 := by
    have hs : (241 : ℝ) ≤ 192 * Real.sqrt 2 := by
      have hsq : (241 : ℝ) ^ 2 ≤ (192 * Real.sqrt 2) ^ 2 := by
        rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have habs : |(241 : ℝ)| ≤ |192 * Real.sqrt 2| := (sq_le_sq).1 hsq
      have hnonneg : 0 ≤ 192 * Real.sqrt 2 := by positivity
      simpa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 241), abs_of_nonneg hnonneg] using habs
    have hcross : (3 : ℝ) * 255 ≤ 4 * (131 + 48 * Real.sqrt 2) := by
      linarith
    have hpos : (0 : ℝ) < 255 := by norm_num
    have hpos4 : (0 : ℝ) < 4 := by norm_num
    -- 3/4 ≤ N/255 from 3*255 ≤ 4*N
    rw [div_le_div_iff₀ hpos4 hpos]
    simpa [mul_comm] using hcross
  -- chain
  have hlow :
      (131 + 48 * Real.sqrt 2) / 255 ≤
        (∫ t in (0 : ℝ)..1, f t) + (∫ t in (1 : ℝ)..2, f t) + ∫ t in (2 : ℝ)..4, f t := by
    rw [← hsum]
    -- i01 is (1/2) * ... which matches the first summand after rewriting 1/c
    have e01 : ∫ t in (0 : ℝ)..1, Real.sqrt t / 2 =
        (1 / 2) * ((1 ^ (3 / 2 : ℝ) - 0 ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ)) := by
      simpa [one_div] using i01
    have e12 : ∫ t in (1 : ℝ)..2, Real.sqrt t / 5 =
        (1 / 5) * ((2 ^ (3 / 2 : ℝ) - 1 ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ)) := by
      simpa [one_div] using i12
    have e24 : ∫ t in (2 : ℝ)..4, Real.sqrt t / 17 =
        (1 / 17) * ((4 ^ (3 / 2 : ℝ) - 2 ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ)) := by
      simpa [one_div] using i24
    calc
      (1 / 2) * ((1 ^ (3 / 2 : ℝ) - 0 ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ))
          + (1 / 5) * ((2 ^ (3 / 2 : ℝ) - 1 ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ))
          + (1 / 17) * ((4 ^ (3 / 2 : ℝ) - 2 ^ (3 / 2 : ℝ)) / (3 / 2 : ℝ))
          = (∫ t in (0 : ℝ)..1, Real.sqrt t / 2) + (∫ t in (1 : ℝ)..2, Real.sqrt t / 5)
              + ∫ t in (2 : ℝ)..4, Real.sqrt t / 17 := by
            rw [e01, e12, e24]
      _ ≤ (∫ t in (0 : ℝ)..1, f t) + (∫ t in (1 : ℝ)..2, f t) + ∫ t in (2 : ℝ)..4, f t := by
            gcongr <;> first | exact hmono01 | exact hmono12 | exact hmono24 | gcongr
  have hadd3 :
      (∫ t in (0 : ℝ)..1, f t) + (∫ t in (1 : ℝ)..2, f t) + ∫ t in (2 : ℝ)..4, f t
        = ∫ t in (0 : ℝ)..4, f t := by
    calc
      (∫ t in (0 : ℝ)..1, f t) + (∫ t in (1 : ℝ)..2, f t) + ∫ t in (2 : ℝ)..4, f t
          = (∫ t in (0 : ℝ)..1, f t) + ((∫ t in (1 : ℝ)..2, f t) + ∫ t in (2 : ℝ)..4, f t) := by
            abel
      _ = (∫ t in (0 : ℝ)..1, f t) + ∫ t in (1 : ℝ)..4, f t := by rw [hadd12]
      _ = ∫ t in (0 : ℝ)..4, f t := hadd04
  calc
    (3 / 4 : ℝ) ≤ (131 + 48 * Real.sqrt 2) / 255 := hnum
    _ ≤ (∫ t in (0 : ℝ)..1, f t) + (∫ t in (1 : ℝ)..2, f t) + ∫ t in (2 : ℝ)..4, f t := hlow
    _ = ∫ t in (0 : ℝ)..4, f t := hadd3
    _ = ∫ t in (0 : ℝ)..4, Real.sqrt t / (1 + t ^ 2) := by rfl
