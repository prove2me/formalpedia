-- Prove2me | Definitions.Def_Probability_RefractoryGrowthRate
-- name    : Probability_RefractoryGrowthRate
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:11.590378+00:00
-- url     : https://prove2.me/theorems/6601ad35-77db-40f7-8537-6b074528058b
-- title:
--   Aether Catalog definitions — Probability_RefractoryGrowthRate
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.RefractoryGrowthRate`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/RefractoryGrowthRate.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
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

namespace Catalog.Probability.NeuralCoding.Temporal

open Filter Topology

/-! ## 1.  The characteristic root -/

/-- The characteristic function `x ↦ x ^ r * (x - 1)`; the refractory growth rate is
its unique solution of `f x = 1` on `[1, ∞)`. -/
noncomputable def charFn (r : ℕ) (x : ℝ) : ℝ := x ^ r * (x - 1)


theorem continuous_charFn (r : ℕ) : Continuous (charFn r) := by
  unfold charFn
  fun_prop

/-- The characteristic equation `x ^ r * (x - 1) = 1` has a solution in `[1, 2]`. -/
theorem exists_charFn_eq_one (r : ℕ) : ∃ x ∈ Set.Icc (1 : ℝ) 2, charFn r x = 1 := by
  have hcont : ContinuousOn (charFn r) (Set.Icc (1 : ℝ) 2) :=
    (continuous_charFn r).continuousOn
  have h1 : charFn r 1 = 0 := by simp [charFn]
  have h2 : charFn r 2 = 2 ^ r := by norm_num [charFn]
  have hmem : (1 : ℝ) ∈ Set.Icc (charFn r 1) (charFn r 2) := by
    rw [h1, h2]
    exact ⟨by norm_num, one_le_pow₀ (by norm_num)⟩
  have := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont hmem
  obtain ⟨x, hx, hxeq⟩ := this
  exact ⟨x, hx, hxeq⟩

/-- **The refractory growth rate** `λ_r`: the unique `x ≥ 1` solving
`x ^ r * (x - 1) = 1`, equivalently `x ^ (r + 1) = x ^ r + 1`. -/
noncomputable def lamR (r : ℕ) : ℝ := (exists_charFn_eq_one r).choose











/-! ## 2.  Two-sided bounds on the capacity -/



/-! ## 3.  The growth rate -/






/-! ## 4.  Monotonicity in the refractory period -/




/-! ## 5.  Numerics for the two-bin refractory period -/



end Catalog.Probability.NeuralCoding.Temporal


