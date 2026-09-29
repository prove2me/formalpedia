-- Prove2me | solution 1 for UniversalRedundancy.bernoulli_price_lower_bits
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:16:24.156233+00:00
-- url     : https://prove2.me/submissions/62e3295e-7b28-459e-8bcc-d70e7ba05ac2

-- Sol generated from MachineLearning/UniversalRedundancy/Bernoulli.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Bernoulli
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_sqrt_le_shtarkovSum_bernoulli
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




/-! ## Types of binary strings -/





/-! ## The Bernoulli class and its Shtarkov sum -/





/-! ## Matching upper bound and the sandwich -/




open UniversalRedundancy in
theorem solution(n : ℕ) (hn : 2 ≤ n) :
    (1 / 2) * logb 2 n - 2 ≤ logb 2 (iidClass Bool n).shtarkovSum := by
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
  have hsn : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hle := sqrt_le_shtarkovSum_bernoulli n hn
  have hlog : logb 2 (Real.sqrt n / 4) ≤ logb 2 (iidClass Bool n).shtarkovSum :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hle
  have hsplit : logb 2 (Real.sqrt n / 4) = (1/2) * logb 2 n - 2 := by
    rw [Real.logb_div (by positivity) (by norm_num)]
    have h1 : logb 2 (Real.sqrt n) = (1/2) * logb 2 n := by
      unfold Real.logb
      rw [Real.log_sqrt hnR.le]
      ring
    have h2 : logb 2 (4:ℝ) = 2 := by
      rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      ring
    rw [h1, h2]
  linarith [hsplit ▸ hlog]
