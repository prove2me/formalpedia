-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.card_trainsR_le_lamR
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:21:01.289131+00:00
-- url     : https://prove2.me/submissions/3ccf825a-8c89-44e6-aa5d-63ad084f3100

-- Sol generated from Probability/RefractoryGrowthRate.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
import Definitions.Def_Probability_RefractoryGrowthRate
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_card_trainsR_recursion
import Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_card_trainsR_small
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The exact growth rate of refractory temporal codes

`RefractoryGeneralized.lean` proved the combinatorial half of the refractory
capacity problem: the number `c_r(n) = (trainsR r n).card` of admissible spike
trains in a window of `n` bins, for a neuron with an `r`-bin refractory period,
satisfies

`c_r(n) = n + 1` for `n ≤ r`,   `c_r(n + r + 1) = c_r(n + r) + c_r(n)`,

whose characteristic equation is `x ^ (r + 1) = x ^ r + 1`.  Only crude rate
bounds (`c_r((r+1)m) ≤ (2^r + 1)^m`) were available there.

This file settles the *analytic* half: the exponential growth rate of `c_r` is
exactly the root of the characteristic equation.

## Main definitions

* `lamR r` : the unique real `x ≥ 1` with `x ^ r * (x - 1) = 1`, equivalently
  `x ^ (r + 1) = x ^ r + 1`.  It lies in `(1, 2]`.

## Main results

* `lamR_unique` : uniqueness of the root, and `lamR_one_eq_goldenRatio`,
  `lamR_zero` : `λ_0 = 2`, `λ_1 = φ`.
* `card_trainsR_le_lamR`, `lamR_le_card_trainsR` : the two-sided bound
  `λ_r ^ n ≤ λ_r ^ r * c_r(n)` and `c_r(n) ≤ (r + 1) * λ_r ^ n`.
* `tendsto_log_card_trainsR` : `log c_r(n) / n → log λ_r`;
  `tendsto_card_trainsR_rpow` : `c_r(n) ^ (1/n) → λ_r`;
  `tendsto_temporal_rate` : the bit rate `log₂ c_r(n) / n → log₂ λ_r`.
* `lamR_strictAnti` : `λ_{r+1} < λ_r` — a longer refractory period strictly
  lowers the rate — and `tendsto_lamR_one` : `λ_r → 1`, so the rate tends to `0`.
* `lamR_two_bounds` : `1.46 < λ_2 < 1.47`, hence a rate of about `0.55` bits per
  bin, well below the `2/3` upper bound proved earlier.
-/

open Catalog.Probability.NeuralCoding.Temporal

open Filter Topology

/-! ## 1.  The characteristic root -/






theorem lamR_mem_Icc (r : ℕ) : lamR r ∈ Set.Icc (1 : ℝ) 2 :=
  (exists_charFn_eq_one r).choose_spec.1

theorem charFn_lamR (r : ℕ) : charFn r (lamR r) = 1 :=
  (exists_charFn_eq_one r).choose_spec.2

theorem lamR_spec (r : ℕ) : (lamR r) ^ r * (lamR r - 1) = 1 := charFn_lamR r

theorem one_lt_lamR (r : ℕ) : 1 < lamR r := by
  rcases lt_or_eq_of_le (lamR_mem_Icc r).1 with h | h
  · exact h
  · exfalso
    have := lamR_spec r
    rw [← h] at this
    norm_num at this



/-- The characteristic equation in the form used by the capacity recursion. -/
theorem lamR_pow_succ (r : ℕ) : (lamR r) ^ (r + 1) = (lamR r) ^ r + 1 := by
  have h := lamR_spec r
  have : (lamR r) ^ r * lamR r - (lamR r) ^ r = 1 := by rw [← h]; ring
  rw [pow_succ]
  linarith




/-! ## 2.  Two-sided bounds on the capacity -/



/-! ## 3.  The growth rate -/






/-! ## 4.  Monotonicity in the refractory period -/




/-! ## 5.  Numerics for the two-bin refractory period -/




open Catalog.Probability.NeuralCoding.Temporal in
theorem solution(r : ℕ) :
    ∀ n : ℕ, ((trainsR r n).card : ℝ) ≤ (r + 1) * (lamR r) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ r
    · rw [card_trainsR_small r n hn]
      have hpow : (1 : ℝ) ≤ (lamR r) ^ n := one_le_pow₀ (one_lt_lamR r).le
      have : ((n : ℝ) + 1) ≤ ((r : ℝ) + 1) := by
        have : (n : ℝ) ≤ (r : ℝ) := by exact_mod_cast hn
        linarith
      calc ((n : ℕ) + 1 : ℕ) = ((n : ℝ) + 1) := by push_cast; ring
        _ ≤ ((r : ℝ) + 1) := this
        _ = ((r : ℝ) + 1) * 1 := by ring
        _ ≤ ((r : ℝ) + 1) * (lamR r) ^ n := by
            apply mul_le_mul_of_nonneg_left hpow (by positivity)
    · obtain ⟨m, hm⟩ : ∃ m, n = m + r + 1 := ⟨n - r - 1, by omega⟩
      subst hm
      have h1 := ih (m + r) (by omega)
      have h2 := ih m (by omega)
      have hrec := card_trainsR_recursion r m
      have hcast : ((trainsR r (m + r + 1)).card : ℝ)
          = ((trainsR r (m + r)).card : ℝ) + ((trainsR r m).card : ℝ) := by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hrec
      rw [hcast]
      have hkey : ((r : ℝ) + 1) * (lamR r) ^ (m + r) + ((r : ℝ) + 1) * (lamR r) ^ m
          = ((r : ℝ) + 1) * (lamR r) ^ (m + r + 1) := by
        have : (lamR r) ^ (m + r + 1) = (lamR r) ^ m * (lamR r) ^ (r + 1) := by
          rw [← pow_add]; ring_nf
        rw [this, lamR_pow_succ]
        have : (lamR r) ^ (m + r) = (lamR r) ^ m * (lamR r) ^ r := by rw [← pow_add]
        rw [this]; ring
      linarith
