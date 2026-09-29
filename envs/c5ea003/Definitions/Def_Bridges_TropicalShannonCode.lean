-- Prove2me | Definitions.Def_Bridges_TropicalShannonCode
-- name    : Bridges_TropicalShannonCode
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:07.292963+00:00
-- url     : https://prove2.me/theorems/b89ca3fa-90a8-47af-9fa8-0f73ab4a7605
-- title:
--   Aether Catalog definitions — Bridges_TropicalShannonCode
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalShannonCode`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalShannonCode.lean by skeleton subtraction
import Mathlib
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

namespace TropicalShannonCode

/-! ## Probability Distributions -/

/-- A finitely-supported probability distribution. -/
structure FinProbDist (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  mass_sum_one : ∑ x : α, mass x = 1

variable {α : Type*} [Fintype α] [Nonempty α]


/-! ## Shannon Entropy (for positive distributions) -/

/-- Shannon entropy H(μ) = -∑ p(x) · log(p(x)), using natural logarithm. -/
noncomputable def shannonEntropy (μ : FinProbDist α) : ℝ :=
  -∑ a : α, μ.mass a * Real.log (μ.mass a)

/-! ## Kraft Admissibility -/

/-- A code length ℓ : α → ℝ is Kraft-admissible if ∑ exp(-ℓ(a)) ≤ 1. -/
def KraftAdmissible (ℓ : α → ℝ) : Prop :=
  ∑ a : α, Real.exp (-ℓ a) ≤ 1

/-- Kraft feasibility for integer code lengths. -/
def TropicalPrefixCode (L : α → ℕ) : Prop :=
  KraftAdmissible (fun a => (L a : ℝ))

/-! ## Core Definitions -/

/-- Tropical self-information: the ideal real-valued code length -log(p). -/
noncomputable def tropInfo (μ : FinProbDist α) (a : α) : ℝ :=
  -Real.log (μ.mass a)

/-- Shannon code length: the rounded-up tropical self-information. -/
noncomputable def shannonLen (μ : FinProbDist α) (a : α) : ℕ :=
  Nat.ceil (tropInfo μ a)

/-- Expected code length under distribution μ. -/
noncomputable def expectedLen (μ : FinProbDist α) (L : α → ℕ) : ℝ :=
  ∑ a, μ.mass a * (L a : ℝ)

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

/-- Min-plus convolution of two functions on ℕ. -/
noncomputable def minPlusConv (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ⨅ (p : Fin (n + 1)), f p.val + g (n - p.val)

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


end TropicalShannonCode


