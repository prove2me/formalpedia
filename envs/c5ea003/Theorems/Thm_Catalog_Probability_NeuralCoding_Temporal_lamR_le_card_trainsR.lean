-- Prove2me | Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_lamR_le_card_trainsR
-- name    : Catalog.Probability.NeuralCoding.Temporal.lamR_le_card_trainsR
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:01:37.509066+00:00
-- url     : https://prove2.me/theorems/cc658b00-d409-4ae4-961f-0b6f41dfaff4
-- title:
--   Lower bound.
-- statement:
--   **Lower bound.**  `λ_r ^ n ≤ λ_r ^ r · c_r(n)`.
--
--   ```lean
--   theorem Catalog.Probability.NeuralCoding.Temporal.lamR_le_card_trainsR(r : ℕ) :
--       ∀ n : ℕ, (lamR r) ^ n ≤ (lamR r) ^ r * ((trainsR r n).card : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/RefractoryGrowthRate.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/RefractoryGrowthRate.lean#L173

-- Thm stub generated from Probability/RefractoryGrowthRate.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
import Definitions.Def_Probability_RefractoryGrowthRate
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
















/-! ## 2.  Two-sided bounds on the capacity -/

theorem Catalog.Probability.NeuralCoding.Temporal.lamR_le_card_trainsR(r : ℕ) :
    ∀ n : ℕ, (lamR r) ^ n ≤ (lamR r) ^ r * ((trainsR r n).card : ℝ) := by sorry
