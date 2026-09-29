-- Prove2me | Definitions.Def_Bridges_TropicalArithmeticCoding
-- name    : Bridges_TropicalArithmeticCoding
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:50.243182+00:00
-- url     : https://prove2.me/theorems/18ebf7df-491f-4b36-992d-2c84a3188965
-- title:
--   Aether Catalog definitions — Bridges_TropicalArithmeticCoding
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalArithmeticCoding`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalArithmeticCoding.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Tropical Information Theory Project. All rights reserved.

# Tropical Arithmetic Coding: Shannon-Optimal Min-Plus Compression

## Bridge: Idempotent Analysis ↔ Source Coding ↔ Algorithmic Information

This file establishes that optimal compression is a tropical variational principle.

Key results:
1. `tropical_shannon_lower_bound`: Kraft-admissible ℓ ⟹ H(μ) ≤ E_μ[ℓ].
2. `shannonEntropy_eq_optimal_kraft_length`: `-log p(x)` achieves equality.
3. `kraft_product_admissible`: Independent composition preserves Kraft admissibility.
4. `minEntropy_le_shannonEntropy`: Min-entropy ≤ Shannon entropy.
5. `universal_tropical_code_optimal`: Universal descriptions are tropically optimal.
-/


open Finset Real BigOperators

namespace TropicalCoding

/-! ## Probability Distributions -/

/-- A finitely-supported probability distribution. -/
structure FinProbDist (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  mass_sum_one : ∑ x : α, mass x = 1

variable {α : Type*} [Fintype α] [Nonempty α]


/-- Maximum probability mass. -/
noncomputable def maxMass (μ : FinProbDist α) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty μ.mass




/-- Min-entropy: H_∞(μ) = -log(max_x p(x)). -/
noncomputable def minEntropy (μ : FinProbDist α) : ℝ := -Real.log (maxMass μ)

/-! ## Section 1: Shannon Entropy -/

/-- Shannon entropy H(μ) = -∑ p(x) · log(p(x)), using natural logarithm.
    Convention: 0 · log(0) = 0. -/
noncomputable def shannonEntropy (μ : FinProbDist α) : ℝ :=
  -∑ a : α, if μ.mass a = 0 then 0 else μ.mass a * Real.log (μ.mass a)



/-! ## Section 2: Tropical Kraft Admissibility -/

/-- A code length ℓ : α → ℝ is Kraft-admissible if ∑ exp(-ℓ(a)) ≤ 1. -/
def TropicalKraftAdmissible (ℓ : α → ℝ) : Prop :=
  ∑ a : α, Real.exp (-ℓ a) ≤ 1


/-! ## Section 3: The Shannon Lower Bound (Gibbs Inequality) -/

/-
Key lemma: ∑ p(a) log(exp(-ℓ(a))/p(a)) ≤ ∑ exp(-ℓ(a)) - 1.
-/

/-
**Tropical Shannon Lower Bound**: H(μ) ≤ E_μ[ℓ] for Kraft-admissible ℓ.
-/




/-! ## Section 4: KL Divergence -/

/-- KL divergence D(p ‖ q). -/
noncomputable def klDivergence (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

/-
KL divergence is nonneg.
-/

/-! ## Section 5: Kraft Admissibility Composition -/

/-
Product of Kraft-admissible codes is admissible.
-/

/-! ## Section 6: Min-Entropy ≤ Shannon Entropy -/

/-
Shannon entropy dominates min-entropy.
-/

/-! ## Section 7: Tropical Min-Plus Algebraic Properties -/



/-
Tropical Kraft convexity: min of admissible codes has Kraft sum ≤ 2.
-/

/-! ## Section 8: Universal Tropical Coding -/

/-- A description method. -/
structure DescriptionMethod (α : Type*) where
  descLength : α → ℕ

/-- Universality. -/
def IsUniversal {α : Type*} (U : DescriptionMethod α) : Prop :=
  ∀ M : DescriptionMethod α, ∃ C : ℕ, ∀ x, U.descLength x ≤ M.descLength x + C

/-- Tropical code length. -/
noncomputable def tropicalCodeLength {α : Type*} (M : DescriptionMethod α) (x : α) : ℝ :=
  (M.descLength x : ℝ)



/-! ## Section 9: Gibbs / Statistical Mechanics -/



/-! ## Section 10: Bridge Theorems -/



/-! ## Section 11: Min-Plus Convolution -/

/-- Min-plus convolution: (f ⋆ₜ g)(z) = inf_x (f(x) + g(z - x)). -/
noncomputable def tropicalConvolution [DecidableEq α] [AddCommGroup α]
    (f g : α → ℝ) : α → ℝ :=
  fun z => ⨅ x : α, f x + g (z - x)

/-
Min-plus convolution is bounded above by any decomposition.
-/

end TropicalCoding


