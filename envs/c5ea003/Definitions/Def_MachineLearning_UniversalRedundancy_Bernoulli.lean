-- Prove2me | Definitions.Def_MachineLearning_UniversalRedundancy_Bernoulli
-- name    : MachineLearning_UniversalRedundancy_Bernoulli
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:31.265864+00:00
-- url     : https://prove2.me/theorems/65d52061-e481-4c7c-ba32-8565d2a3d52c
-- title:
--   Aether Catalog definitions — MachineLearning_UniversalRedundancy_Bernoulli
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.UniversalRedundancy.Bernoulli`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/UniversalRedundancy/Bernoulli.lean by skeleton subtraction
import Mathlib
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

namespace UniversalRedundancy

/-! ## Two-sided Stirling bounds -/




/-! ## Types of binary strings -/

/-- The number of ones in a binary string. -/
def ones {n : ℕ} (x : Fin n → Bool) : ℕ := (univ.filter (fun i => x i = true)).card




/-! ## The Bernoulli class and its Shtarkov sum -/

/-- The maximum-likelihood Bernoulli parameter of a string with `k` ones. -/
noncomputable def bernoulliParam (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) : Simplex Bool :=
  ⟨fun b => if b then (k : ℝ) / n else ((n - k : ℕ) : ℝ) / n, by
    intro b
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    cases b <;> simp <;> positivity, by
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hsum : (k : ℝ) + ((n - k : ℕ) : ℝ) = (n : ℝ) := by
      have hnat : k + (n - k : ℕ) = n := by omega
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hnat
    have hkey : (k : ℝ) / n + ((n - k : ℕ) : ℝ) / n = 1 := by
      rw [← add_div, hsum, div_self hnR.ne']
    simpa [Fintype.sum_bool] using hkey⟩




/-! ## Matching upper bound and the sandwich -/



end UniversalRedundancy


