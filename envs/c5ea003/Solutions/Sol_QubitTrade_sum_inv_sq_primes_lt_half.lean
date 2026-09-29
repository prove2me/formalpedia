-- Prove2me | solution 1 for QubitTrade.sum_inv_sq_primes_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T12:03:20.601671+00:00
-- url     : https://prove2.me/submissions/f2583f9e-6c3b-481d-8e68-52773c501663

import Mathlib
import Definitions.Def_Algebra_QubitTrade_RecordCount
open QubitTrade Finset in
theorem solution (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ∑ p ∈ S, (1:ℚ) / (p : ℚ) ^ 2 < 1 / 2 := by
  -- telescoping: `Σ_{2 ≤ k < M} (1/k − 1/(k+1)) = 1/2 − 1/M`
  have htel : ∀ M : ℕ, 2 ≤ M → ∑ k ∈ Ico 2 M, ((1:ℚ) / k - 1 / (k + 1)) = 1 / 2 - 1 / M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [sum_Ico_succ_top hM, ih]
      have : (M : ℚ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  rw [← sum_filter_add_sum_filter_not S (fun p => p < 5)]
  -- the primes below `5` are `2` and `3`
  have hsmall : ∑ p ∈ S.filter (fun p => p < 5), (1:ℚ) / (p : ℚ) ^ 2 ≤ 1 / 4 + 1 / 9 := by
    have hsub : S.filter (fun p => p < 5) ⊆ {2, 3} := by
      intro p hp
      rw [mem_filter] at hp
      have hpr := hS p hp.1
      have h2 := hpr.two_le
      have h4 : p ≠ 4 := by rintro rfl; exact absurd hpr (by norm_num)
      simp only [mem_insert, mem_singleton]
      omega
    calc _ ≤ ∑ p ∈ ({2, 3} : Finset ℕ), (1:ℚ) / (p : ℚ) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 / 4 + 1 / 9 := by norm_num
  -- a prime `p ≥ 5` is `2k+1` with `k ≥ 2`, and `1/(2k+1)² ≤ (1/k − 1/(k+1))/4`
  set g : ℕ → ℚ := fun k => ((1:ℚ) / k - 1 / (k + 1)) / 4 with hg
  have hodd : ∀ p ∈ S.filter (fun p => ¬ p < 5), p % 2 = 1 ∧ 5 ≤ p := by
    intro p hp
    rw [mem_filter] at hp
    have hpr := hS p hp.1
    exact ⟨Nat.odd_iff.mp (hpr.odd_of_ne_two (by omega)), by omega⟩
  have hgpos : ∀ k : ℕ, 1 ≤ k → 0 ≤ g k := by
    intro k hk
    have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
    simp only [hg]
    rw [div_sub_div _ _ (by positivity) (by positivity)]
    apply div_nonneg (div_nonneg (by linarith) (by positivity)) (by norm_num)
  have hterm : ∀ p ∈ S.filter (fun p => ¬ p < 5), (1:ℚ) / (p : ℚ) ^ 2 ≤ g ((p - 1) / 2) := by
    intro p hp
    obtain ⟨h1, h5⟩ := hodd p hp
    obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
    have hk : (2 * k + 1 - 1) / 2 = k := by omega
    rw [hk]
    have hk2 : (2 : ℚ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
    have hgk : g k = 1 / (4 * (k : ℚ) * (k + 1)) := by
      simp only [hg]
      field_simp
      ring
    rw [hgk]
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  -- sum over the large primes via the injective map `p ↦ (p−1)/2` into `[2, M)`
  set M := S.sup id + 2 with hM
  have hlarge : ∑ p ∈ S.filter (fun p => ¬ p < 5), (1:ℚ) / (p : ℚ) ^ 2 ≤ 1 / 8 := by
    calc _ ≤ ∑ p ∈ S.filter (fun p => ¬ p < 5), g ((p - 1) / 2) := sum_le_sum hterm
      _ = ∑ k ∈ (S.filter (fun p => ¬ p < 5)).image (fun p => (p - 1) / 2), g k := by
          rw [sum_image]
          intro p hp q hq hpq
          have := hodd p hp
          have := hodd q hq
          simp only at hpq
          omega
      _ ≤ ∑ k ∈ Ico 2 M, g k := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro k hk
            obtain ⟨p, hp, rfl⟩ := mem_image.mp hk
            have := hodd p hp
            have hle : p ≤ S.sup id := le_sup (f := id) (mem_filter.mp hp).1
            rw [mem_Ico]
            omega
          · intro k hk _
            exact hgpos k (by rw [mem_Ico] at hk; omega)
      _ = (1 / 2 - 1 / M) / 4 := by
          rw [hg, ← sum_div, htel M (by omega)]
      _ ≤ 1 / 8 := by
          have : (0 : ℚ) ≤ 1 / M := by positivity
          linarith
  linarith
