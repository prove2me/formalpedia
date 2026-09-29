-- Prove2me | solution 1 for UniversalRedundancy.sqrt_le_shtarkovSum_bernoulli
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:14:25.394926+00:00
-- url     : https://prove2.me/submissions/6a36642e-e7f2-467e-90eb-17a77bde6c89

-- Sol generated from MachineLearning/UniversalRedundancy/Bernoulli.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Bernoulli
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_SourceClass_le_maxLik
import Theorems.Thm_UniversalRedundancy_SourceClass_maxLik_nonneg
import Theorems.Thm_UniversalRedundancy_card_ones_fiber
import Theorems.Thm_UniversalRedundancy_prod_eq_prod_pow_countStat
import Theorems.Thm_UniversalRedundancy_type_term_lower
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


/-- The likelihood of a string under its own maximum-likelihood parameter. -/
lemma prob_bernoulliParam {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (iidClass Bool n).prob (bernoulliParam n (ones x) hn (ones_le x)) x
      = ((ones x : ℝ) / n) ^ (ones x) * (((n - ones x : ℕ) : ℝ) / n) ^ (n - ones x) := by
  classical
  have hprod := prod_eq_prod_pow_countStat
    (g := fun b : Bool => (bernoulliParam n (ones x) hn (ones_le x)).1 b) (w := x)
  simp only [iidClass]
  rw [hprod, Fintype.prod_bool]
  have hct : ((countStat x true : Fin (n+1)) : ℕ) = ones x := rfl
  have hcf : ((countStat x false : Fin (n+1)) : ℕ) = n - ones x := card_zeros x
  rw [hct, hcf]
  simp only [bernoulliParam]
  norm_num



/-! ## Matching upper bound and the sandwich -/




open UniversalRedundancy in
theorem solution(n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt n / 4 ≤ (iidClass Bool n).shtarkovSum := by
  classical
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
  have hsn : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  set F : ℕ → Finset (Fin n → Bool) :=
    fun k => univ.filter (fun x : Fin n → Bool => ones x = k) with hF
  -- each fibre contributes at least 1/(2√n)
  have hfibre : ∀ k ∈ Finset.Icc 1 (n - 1),
      1 / (2 * Real.sqrt n) ≤ ∑ x ∈ F k, (iidClass Bool n).maxLik x := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hkn : k < n := by omega
    set j := n - k with hj
    have hj1 : 1 ≤ j := by omega
    have hkj : k + j = n := by omega
    have hterm : ∀ x ∈ F k, ((k : ℝ) / n) ^ k * ((j : ℝ) / n) ^ j
        ≤ (iidClass Bool n).maxLik x := by
      intro x hx
      have hox : ones x = k := (Finset.mem_filter.mp hx).2
      have hp := prob_bernoulliParam hn0 x
      have hle := (iidClass Bool n).le_maxLik
        (bernoulliParam n (ones x) hn0 (ones_le x)) x
      rw [hp] at hle
      rw [hox] at hle
      have hnk : n - k = j := by omega
      rw [hnk] at hle
      exact hle
    have hcard : (F k).card = n.choose k := by rw [hF]; exact card_ones_fiber n k
    have hsum : ((n.choose k : ℕ) : ℝ) * (((k : ℝ) / n) ^ k * ((j : ℝ) / n) ^ j)
        ≤ ∑ x ∈ F k, (iidClass Bool n).maxLik x := by
      calc ((n.choose k : ℕ) : ℝ) * (((k : ℝ) / n) ^ k * ((j : ℝ) / n) ^ j)
          = ∑ _x ∈ F k, ((k : ℝ) / n) ^ k * ((j : ℝ) / n) ^ j := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ ≤ ∑ x ∈ F k, (iidClass Bool n).maxLik x :=
            Finset.sum_le_sum fun x hx => hterm x hx
    have hlow := type_term_lower k j hk1 hj1
    have hcast : ((k + j : ℕ) : ℝ) = (n : ℝ) := by rw [hkj]
    rw [hcast, hkj] at hlow
    calc 1 / (2 * Real.sqrt n) ≤ ((n.choose k : ℕ) : ℝ) * ((k:ℝ)/(n:ℝ))^k * ((j:ℝ)/(n:ℝ))^j :=
          hlow
      _ = ((n.choose k : ℕ) : ℝ) * (((k : ℝ) / n) ^ k * ((j : ℝ) / n) ^ j) := by ring
      _ ≤ ∑ x ∈ F k, (iidClass Bool n).maxLik x := hsum
  -- the fibres are disjoint
  have hdisj : (↑(Finset.Icc 1 (n-1)) : Set ℕ).PairwiseDisjoint F := by
    intro k _ l _ hkl
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    have h1 : ones x = k := (Finset.mem_filter.mp hx).2
    have h2 : ones x = l := (Finset.mem_filter.mp hx').2
    exact hkl (h1 ▸ h2 ▸ rfl)
  have hunion : ∑ k ∈ Finset.Icc 1 (n-1), ∑ x ∈ F k, (iidClass Bool n).maxLik x
      ≤ (iidClass Bool n).shtarkovSum := by
    rw [← Finset.sum_biUnion hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun x _ _ => (iidClass Bool n).maxLik_nonneg x
  have hcount : ((Finset.Icc 1 (n-1)).card : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.card_Icc]
    have : n - 1 + 1 - 1 = n - 1 := by omega
    rw [this]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : (1 : ℕ) ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    exact hcast
  have hsum_low : ((n : ℝ) - 1) * (1 / (2 * Real.sqrt n))
      ≤ ∑ k ∈ Finset.Icc 1 (n-1), ∑ x ∈ F k, (iidClass Bool n).maxLik x := by
    calc ((n : ℝ) - 1) * (1 / (2 * Real.sqrt n))
        = ∑ _k ∈ Finset.Icc 1 (n-1), 1 / (2 * Real.sqrt n) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcount]
      _ ≤ ∑ k ∈ Finset.Icc 1 (n-1), ∑ x ∈ F k, (iidClass Bool n).maxLik x :=
          Finset.sum_le_sum hfibre
  have hnn : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hfinal : Real.sqrt n / 4 ≤ ((n : ℝ) - 1) * (1 / (2 * Real.sqrt n)) := by
    refine le_of_mul_le_mul_right ?_ (by positivity : (0:ℝ) < 2 * Real.sqrt n)
    have h1 : Real.sqrt n / 4 * (2 * Real.sqrt n) = (n:ℝ)/2 := by
      field_simp
      nlinarith [hnn]
    have h2 : ((n:ℝ)-1) * (1 / (2 * Real.sqrt n)) * (2 * Real.sqrt n) = (n:ℝ)-1 := by
      field_simp
    rw [h1, h2]
    linarith
  linarith [hfinal, hsum_low, hunion]
