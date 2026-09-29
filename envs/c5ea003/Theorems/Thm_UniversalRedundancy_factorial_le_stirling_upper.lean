-- Prove2me | Theorems.Thm_UniversalRedundancy_factorial_le_stirling_upper
-- name    : UniversalRedundancy.factorial_le_stirling_upper
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:59:35.115347+00:00
-- url     : https://prove2.me/theorems/cff51d90-52c0-49fc-819d-43968277f6f7
-- title:
--   Explicit Stirling upper bound: `m!
-- statement:
--   Explicit Stirling upper bound: `m! ≤ e·√m·(m/e)^m` for `m ≥ 1`, obtained
--   from the antitonicity of Mathlib's Stirling sequence.
--
--   ```lean
--   theorem UniversalRedundancy.factorial_le_stirling_upper(m : ℕ) (hm : 1 ≤ m) :
--       (Nat.factorial m : ℝ) ≤ Real.exp 1 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/UniversalRedundancy/Bernoulli.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/UniversalRedundancy/Bernoulli.lean#L58

-- Thm stub generated from MachineLearning/UniversalRedundancy/Bernoulli.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Bernoulli
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality V: the Rissanen `½ log n` lower bound

The falsifiability gate of the research thread: the upper bounds of
`UniversalRedundancy.Types` must be matched by a lower bound of the *known
minimax rate*.  For a `d`-parameter smooth class the classical rate is
`(d/2) log₂ n`.  Here we prove it, with explicit constants and no asymptotics,
for the one-parameter case `d = 1`: the memoryless binary (Bernoulli) class.

## Central Idea

By Part I the minimax redundancy is `log₂ Cₛ` with `Cₛ = ∑ₓ sup_θ p_θ x`.  For
the Bernoulli class the maximum likelihood of a string with `k` ones is
`(k/n)^k ((n-k)/n)^{n-k}`, and strings of the same *type* form a fibre of size
`C(n,k)`.  Two-sided Stirling bounds — Mathlib's `√(2πn)(n/e)^n ≤ n!` and the
antitonicity of the Stirling sequence, which gives `n! ≤ e √n (n/e)^n` — turn
each fibre contribution into

`C(n,k) (k/n)^k ((n-k)/n)^{n-k} ≥ √(2πn) / (e² √k √(n-k)) ≥ 1/(2√n)`,

and summing the `n-1` interior types gives `Cₛ ≥ (n-1)/(2√n) ≥ √n / 4`.

Hence the price of universality for the binary memoryless class is at least
`½ log₂ n − 2` bits — the Rissanen rate `(d/2) log₂ n` with `d = 1` — while
Part II gives the upper bound `2 log₂ (n+1)`.  Universality is therefore *not*
free, but it is only logarithmically expensive.

## Main Results

* `factorial_le_stirling_upper` — `m! ≤ e √m (m/e)^m` for `m ≥ 1`
* `type_term_lower` — every interior type contributes at least `1/(2√n)`
* `card_ones_fiber` — the type fibre `{x : Fin n → Bool | #ones = k}` has
  `C(n,k)` elements
* `sqrt_le_shtarkovSum_bernoulli` — `√n / 4 ≤ Cₛ` for the binary memoryless
  class, `n ≥ 2`
* `bernoulli_price_lower_bits` — every Kraft-compliant code pays at least
  `½ log₂ n − 2` bits of redundancy on some message against some Bernoulli
  source: the Rissanen rate is unavoidable
* `bernoulli_price_sandwich` — the two-sided statement
  `½ log₂ n − 2 ≤ log₂ Cₛ ≤ 2 log₂ (n+1)`

## Application Keywords

Rissanen redundancy, Stirling bounds, method of types, minimax lower bound,
Bernoulli class, universal coding
-/


open Finset Real

open UniversalRedundancy

/-! ## Two-sided Stirling bounds -/

theorem UniversalRedundancy.factorial_le_stirling_upper(m : ℕ) (hm : 1 ≤ m) :
    (Nat.factorial m : ℝ) ≤ Real.exp 1 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m := by sorry
