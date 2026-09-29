-- Prove2me | solution 1 for UniversalRedundancy.factorial_le_stirling_upper
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:25:05.499203+00:00
-- url     : https://prove2.me/submissions/d80e2179-7164-4054-be84-36f633fb96c7

-- Sol generated from MachineLearning/UniversalRedundancy/Bernoulli.lean
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




/-! ## Types of binary strings -/





/-! ## The Bernoulli class and its Shtarkov sum -/





/-! ## Matching upper bound and the sandwich -/




open UniversalRedundancy in
theorem solution(m : ℕ) (hm : 1 ≤ m) :
    (Nat.factorial m : ℝ) ≤ Real.exp 1 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le t)
  simp only [Function.comp] at h
  rw [Stirling.stirlingSeq_one] at h
  unfold Stirling.stirlingSeq at h
  have hpos : (0:ℝ) < Real.sqrt (2 * ((t+1 : ℕ) : ℝ)) * (((t+1:ℕ):ℝ) / Real.exp 1) ^ (t+1) := by
    have h1 : (0:ℝ) < ((t+1:ℕ) : ℝ) := by positivity
    have h2 : (0:ℝ) < Real.sqrt (2 * ((t+1 : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  rw [div_le_iff₀ hpos] at h
  refine le_trans h (le_of_eq ?_)
  have hs : Real.sqrt (2 * ((t+1 : ℕ) : ℝ)) = Real.sqrt 2 * Real.sqrt ((t+1:ℕ) : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  rw [hs]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
