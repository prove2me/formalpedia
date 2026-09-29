-- Prove2me | solution 1 for TropicalShannonCode.shannon_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:33.581858+00:00
-- url     : https://prove2.me/submissions/88c06a4e-6a89-452b-b740-287f11399ecf

-- Sol generated from Bridges/TropicalShannonCode.lean
import Mathlib
import Definitions.Def_Bridges_TropicalShannonCode
/-
Copyright (c) 2025 Tropical Information Theory Project. All rights reserved.

# Tropical Shannon Code: Near-Optimal Min-Plus Compression

This file establishes the core bridge between tropical (min-plus) algebra
and Shannon source coding theory. The main results are:

1. **Theorem A** (`tropical_shannon_code_near_optimal`):
   The rounded tropical self-information code ⌈-log μ(a)⌉ has expected length
   sandwiched between entropy H(μ) and H(μ)+1.

2. **Theorem B** (`tropical_code_expected_length_sandwich`):
   There exists a Kraft-feasible integer code achieving the sandwich bound.

3. **Theorem C** (`minPlusConv_eq_sInf`, `kraft_product_is_tropical_convolution`):
   Min-plus convolution equals the infimum characterization, and product
   Kraft sums decompose as tropical convolution.

4. **Theorem D** (`ceil_neglog_is_least_feasible_majorant`):
   The ceiling of negative log-probability is the least integer code length
   among all feasible majorants of information content.
-/


open Finset Real BigOperators

open TropicalShannonCode

/-! ## Probability Distributions -/


variable {α : Type*} [Fintype α] [Nonempty α]


/-! ## Shannon Entropy (for positive distributions) -/


/-! ## Kraft Admissibility -/



/-! ## Core Definitions -/




/-! ## Helper Lemmas -/

/-
Tropical self-information is nonneg for probability distributions.
-/

/-
The ceiling is at least the value.
-/

/-
The ceiling is strictly less than value + 1.
-/

/-! ## Shannon Code Satisfies Kraft Inequality -/

/-
The Shannon code lengths satisfy the Kraft inequality:
    ∑ exp(-⌈-log p(a)⌉) ≤ 1.
    Proof: exp(-⌈x⌉) ≤ exp(-x) since ⌈x⌉ ≥ x, and ∑ exp(log p(a)) = ∑ p(a) = 1.
-/

/-! ## Gibbs Inequality (Lower Bound) -/

/-
**Gibbs inequality / Shannon lower bound**: For any Kraft-admissible code
    lengths ℓ, the expected code length is at least the Shannon entropy.
    H(μ) ≤ E_μ[ℓ].
-/

/-! ## Theorem A: Tropical Shannon Code Near-Optimality -/

/-
**Upper bound**: Expected Shannon code length < entropy + 1.
    Uses ⌈x⌉ < x + 1 pointwise, then sums with positive weights.
-/


/-! ## Theorem B: Tropical Code Expected Length Sandwich -/


/-! ## Theorem C: Min-Plus Convolution -/


/-
**Theorem C (part 1)**: Min-plus convolution equals the set-theoretic infimum
    characterization {c | ∃ i j, i+j=n ∧ c = f(i)+g(j)}.
-/

/-
Min-plus convolution is commutative.
-/

/-
Min-plus convolution is bounded above by any valid decomposition.
-/

/-
**Theorem C (part 2)**: Product source Kraft sums decompose multiplicatively,
    which in log space becomes min-plus additive — the tropical convolution principle.
    This proves that code combination for independent sources is literally
    tropical algebra.
-/

/-! ## Theorem D: Least Feasible Majorant -/

/-
**Theorem D**: The ceiling of negative log-probability is the least
    feasible integer majorant. Among all integer code lengths that pointwise
    dominate the information content, ⌈-log μ(a)⌉ is pointwise minimal.
    This is the tropical envelope theorem.
-/

/-! ## Bridge Theorem -/



open TropicalShannonCode in
theorem solution    (μ : FinProbDist α) (ℓ : α → ℝ)
    (hpos : ∀ a, 0 < μ.mass a)
    (hKraft : KraftAdmissible ℓ) :
    shannonEntropy μ ≤ ∑ a, μ.mass a * ℓ a := by
  -- Applying the inequality $\log(x) \leq x - 1$ to each term in the sum, we get:
  have h_ineq : ∑ a, (μ.mass a) * (ℓ a + Real.log (μ.mass a)) ≥ ∑ a, (μ.mass a) * Real.log (Real.exp (-ℓ a) / (μ.mass a)) := by
    have h_ineq : ∑ a, (μ.mass a) * (Real.exp (-ℓ a) / (μ.mass a) - 1) ≥ ∑ a, (μ.mass a) * Real.log (Real.exp (-ℓ a) / (μ.mass a)) := by
      exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ( by linarith [ Real.log_le_sub_one_of_pos ( div_pos ( Real.exp_pos ( -ℓ a ) ) ( hpos a ) ) ] ) ( le_of_lt ( hpos a ) );
    simp_all +decide [ mul_sub, mul_add, mul_div_cancel₀ _ ( ne_of_gt ( hpos _ ) ) ];
    simp_all +decide [ Real.log_div ( ne_of_gt ( Real.exp_pos _ ) ) ( ne_of_gt ( hpos _ ) ), Real.log_exp, Finset.sum_add_distrib, mul_add, mul_sub, Finset.sum_sub_distrib ];
    linarith [ μ.mass_sum_one, show ∑ x, Real.exp ( -ℓ x ) ≤ 1 from hKraft ];
  -- Using the properties of logarithms, we can simplify the right-hand side of the inequality.
  have h_simplify : ∑ a, (μ.mass a) * Real.log (Real.exp (-ℓ a) / (μ.mass a)) = ∑ a, (μ.mass a) * (-ℓ a - Real.log (μ.mass a)) := by
    exact Finset.sum_congr rfl fun x _ => by rw [ Real.log_div ( by positivity ) ( by linarith [ hpos x ] ), Real.log_exp ] ;
  simp_all +decide [ mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib ];
  unfold shannonEntropy; linarith;
