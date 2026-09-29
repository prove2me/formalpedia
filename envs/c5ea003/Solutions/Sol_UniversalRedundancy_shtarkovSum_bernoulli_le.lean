-- Prove2me | solution 1 for UniversalRedundancy.shtarkovSum_bernoulli_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:16:25.112642+00:00
-- url     : https://prove2.me/submissions/7378da6a-4fac-4f68-b906-dca9be8adbc0

-- Sol generated from MachineLearning/UniversalRedundancy/Bernoulli.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Bernoulli
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_SourceClass_shtarkovSum_le_card_statistic
import Theorems.Thm_UniversalRedundancy_prod_eq_prod_pow_countStat
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


lemma ones_le {n : ℕ} (x : Fin n → Bool) : ones x ≤ n := by
  unfold ones
  calc (univ.filter (fun i => x i = true)).card ≤ (univ : Finset (Fin n)).card :=
        Finset.card_filter_le _ _
    _ = n := by simp

lemma card_zeros {n : ℕ} (x : Fin n → Bool) :
    (univ.filter (fun i => x i = false)).card = n - ones x := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n))) (p := fun i => x i = true)
  have h2 : (univ.filter (fun i => ¬ (x i = true))) = univ.filter (fun i => x i = false) := by
    refine Finset.filter_congr fun i _ => ?_
    cases x i <;> simp
  rw [h2] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold ones
  omega


/-! ## The Bernoulli class and its Shtarkov sum -/





/-! ## Matching upper bound and the sandwich -/




open UniversalRedundancy in
theorem solution(n : ℕ) :
    (iidClass Bool n).shtarkovSum ≤ ((n : ℝ) + 1) := by
  classical
  have hstat := (iidClass Bool n).shtarkovSum_le_card_statistic
    (T := fun x : Fin n → Bool => (⟨ones x, by have := ones_le x; omega⟩ : Fin (n + 1)))
    ?_
  · refine le_trans hstat (le_of_eq ?_)
    simp
  · intro θ x y hxy
    have hones : ones x = ones y := congrArg Fin.val hxy
    have hx := prod_eq_prod_pow_countStat (g := fun b : Bool => θ.1 b) (w := x)
    have hy := prod_eq_prod_pow_countStat (g := fun b : Bool => θ.1 b) (w := y)
    have hxt : ((countStat x true : Fin (n+1)) : ℕ) = ones x := rfl
    have hyt : ((countStat y true : Fin (n+1)) : ℕ) = ones y := rfl
    have hxf : ((countStat x false : Fin (n+1)) : ℕ) = n - ones x := card_zeros x
    have hyf : ((countStat y false : Fin (n+1)) : ℕ) = n - ones y := card_zeros y
    simp only [iidClass]
    rw [hx, hy, Fintype.prod_bool, Fintype.prod_bool, hxt, hyt, hxf, hyf, hones]
