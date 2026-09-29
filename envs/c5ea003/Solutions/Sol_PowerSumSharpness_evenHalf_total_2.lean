-- Prove2me | solution 2 for PowerSumSharpness.evenHalf_total
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:41:08.673161+00:00
-- url     : https://prove2.me/submissions/ef33b7ac-12c3-47f8-9daf-e395456958b8

import Mathlib
import Definitions.Def_Probability_PowerSumSharpness
open PowerSumSharpness Finset Polynomial in
theorem solution {N : ℕ} (hN : 1 ≤ N) : powerSum N (evenHalf N) 0 = 1 := by
  classical
  have hsplit : ∑ i ∈ Finset.range (N + 1), (N.choose i : ℤ)
      = ∑ i ∈ (Finset.range (N + 1)).filter (fun i => Even i), (N.choose i : ℤ)
        + ∑ i ∈ (Finset.range (N + 1)).filter (fun i => ¬ Even i), (N.choose i : ℤ) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have halt : ∑ i ∈ Finset.range (N + 1), ((-1 : ℤ) ^ i * (N.choose i : ℤ))
      = ∑ i ∈ (Finset.range (N + 1)).filter (fun i => Even i), (N.choose i : ℤ)
        - ∑ i ∈ (Finset.range (N + 1)).filter (fun i => ¬ Even i), (N.choose i : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1)) (fun i => Even i)
      (fun i => (-1 : ℤ) ^ i * (N.choose i : ℤ))]
    have e1 : ∑ i ∈ (Finset.range (N + 1)).filter (fun i => Even i),
        ((-1 : ℤ) ^ i * (N.choose i : ℤ))
        = ∑ i ∈ (Finset.range (N + 1)).filter (fun i => Even i), (N.choose i : ℤ) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hev : Even i := (Finset.mem_filter.mp hi).2
      rw [hev.neg_one_pow, one_mul]
    have e2 : ∑ i ∈ (Finset.range (N + 1)).filter (fun i => ¬ Even i),
        ((-1 : ℤ) ^ i * (N.choose i : ℤ))
        = -∑ i ∈ (Finset.range (N + 1)).filter (fun i => ¬ Even i), (N.choose i : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hod : Odd i := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hi).2
      rw [hod.neg_one_pow]
      ring
    rw [e1, e2]
    ring
  have haltz : ∑ i ∈ Finset.range (N + 1), ((-1 : ℤ) ^ i * (N.choose i : ℤ)) = 0 := by
    rw [Int.alternating_sum_range_choose]
    simp [show N ≠ 0 by omega]
  have htot : ∑ i ∈ Finset.range (N + 1), (N.choose i : ℤ) = 2 ^ N := by
    have := Nat.sum_range_choose N
    exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) this
  have heven : ∑ i ∈ (Finset.range (N + 1)).filter (fun i => Even i), (N.choose i : ℤ)
      = 2 ^ (N - 1) := by
    have h2 : (2 : ℤ) ^ N = 2 * 2 ^ (N - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [haltz] at halt
    omega
  have hevenR : ∑ i ∈ (Finset.range (N + 1)).filter (fun i => Even i), (N.choose i : ℝ)
      = 2 ^ (N - 1) := by
    have := heven
    exact_mod_cast this
  unfold powerSum evenHalf
  simp only [pow_zero, mul_one]
  have e : ∑ i ∈ Finset.range (N + 1),
      (if Even i then (N.choose i : ℝ) / 2 ^ (N - 1) else 0)
      = (∑ i ∈ (Finset.range (N + 1)).filter (fun i => Even i), (N.choose i : ℝ)) / 2 ^ (N - 1) := by
    rw [Finset.sum_div, Finset.sum_filter]
  rw [e, hevenR]
  have hne : (2 : ℝ) ^ (N - 1) ≠ 0 := by positivity
  field_simp
