-- Prove2me | Definitions.Def_Bridges_MinEntropy
-- name    : Bridges_MinEntropy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:08:29.380986+00:00
-- url     : https://prove2.me/theorems/945e89df-87ef-4e09-8d17-1560249a3710
-- title:
--   Aether Catalog definitions — Bridges_MinEntropy
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.MinEntropy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/MinEntropy.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Non-Archimedean Information Theory: Min-Entropy Foundations

## Bridge: Tropical Algebra ↔ Cryptographic Entropy ↔ Idempotent Analysis

Min-entropy H_∞(X) = -log(max_x p(x)) is simultaneously:
- The natural entropy of the tropical (min-plus) semifield (ℝ ∪ {∞}, min, +)
- The fundamental resource for cryptographic randomness extraction
- The worst-case measure for post-quantum security analysis

## Impact: post_quantum_security, certified_robustness, tropical_hash_collision
-/


open Finset Real BigOperators

namespace NonArchInfoTheory

/-- A finitely-supported probability distribution over a finite type α.
    Bridge: connects measure theory to discrete combinatorial probability.
    Impact: foundation for certified_robustness bounds and post_quantum_security. -/
structure FinProbDist (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  mass_sum_one : ∑ x : α, mass x = 1

variable {α : Type*} [Fintype α]



/-! ## Total Variation Distance

These results don't require `Nonempty α`, so we prove them before
introducing that variable. -/

section TotalVariation

variable {α : Type*} [Fintype α]

/-- Total variation distance between two distributions.
    Bridge: connects metric probability theory to information-theoretic stability.
    Impact: lipschitz_certified_robustness — TV distance controls entropy perturbation. -/
noncomputable def totalVariation (μ ν : FinProbDist α) : ℝ :=
  (1 / 2) * ∑ x : α, |μ.mass x - ν.mass x|






end TotalVariation

/-! ## Uniform Distribution -/

/-- The uniform distribution on a nonempty finite type.
    Bridge: connects combinatorics to maximum-entropy principle.
    Impact: post_quantum_security — uniform is the ideal for randomness extraction. -/
noncomputable def uniformDist (α : Type*) [Fintype α] [Nonempty α] : FinProbDist α where
  mass := fun _ => (1 : ℝ) / (Fintype.card α : ℝ)
  mass_nonneg := fun _ => by positivity
  mass_sum_one := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Predicate: a distribution is uniform (all masses equal). -/
def isUniform (μ : FinProbDist α) : Prop :=
  ∀ x y : α, μ.mass x = μ.mass y


/-! ## Maximum Mass -/

variable [Nonempty α]

/-- The maximum probability mass: max_x p(x).
    In the tropical semifield, this is the idempotent sum ⊕ of probabilities.
    Bridge: tropical algebra (⊕ = max) ↔ probability theory. -/
noncomputable def maxMass (μ : FinProbDist α) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty μ.mass






/-! ## Min-Entropy Definition and Properties -/

/-- Min-entropy H_∞(X) = -log(max_x p(x)).
    The fundamental entropy of tropical information theory.
    Bridge: cryptography (min-entropy extractors) ↔ idempotent analysis (Maslov).
    Impact: post_quantum_security — min-entropy quantifies extractable randomness. -/
noncomputable def minEntropy (μ : FinProbDist α) : ℝ :=
  -Real.log (maxMass μ)



/-! ## Deterministic Distribution -/

/-- A deterministic distribution concentrated on one point. -/
noncomputable def deterministicDist [DecidableEq α] (a : α) : FinProbDist α where
  mass := fun x => if x = a then 1 else 0
  mass_nonneg := fun x => by split_ifs <;> linarith
  mass_sum_one := by simp [Finset.sum_ite_eq', Finset.mem_univ]



/-! ## Uniform Distribution Entropy -/



/-! ## Product Distribution -/

variable {β : Type*} [Fintype β] [Nonempty β]

/-- Product distribution of two independent distributions.
    Bridge: independent probability ↔ tensor products in tropical algebra.
    Impact: post_quantum_security — independent components contribute additively. -/
noncomputable def productDist (μ : FinProbDist α) (ν : FinProbDist β) :
    FinProbDist (α × β) where
  mass := fun p => μ.mass p.1 * ν.mass p.2
  mass_nonneg := fun ⟨a, b⟩ => mul_nonneg (μ.mass_nonneg a) (ν.mass_nonneg b)
  mass_sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.mass_sum_one, mul_one, μ.mass_sum_one]

/-
Key lemma: max of product of nonneg functions = product of maxes.
    Bridge: tropical ⊗ distributes over product spaces.
-/



/-! ## Exp-Entropy Identity -/



/-! ## Min-Entropy Characterization -/



/-! ## Tropical Valuation -/



/-! ## Idempotent Entropy Axioms -/


/-! ## Marginal Distributions -/



/-! ## Bernoulli Distribution -/

/-- A Bernoulli distribution with parameter p ∈ [0,1]. -/
noncomputable def bernoulliDist (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FinProbDist (Fin 2) where
  mass := fun i => if i = 0 then p else 1 - p
  mass_nonneg := fun i => by fin_cases i <;> simp <;> linarith
  mass_sum_one := by rw [Fin.sum_univ_two]; simp

/-
Min-entropy of Bernoulli(p) = -log(max(p, 1-p)).
    Bridge: binary entropy ↔ tropical max operation.
    Impact: post_quantum_security — binary source entropy for bit extraction.
-/

/-! ## Counting Lemma -/

/-
|{x : p(x) ≥ t}| ≤ 1/t for t > 0 (Markov-like bound).
    Bridge: counting arguments ↔ tropical probability bounds.
    Impact: certified_robustness — bounds support size above threshold.
-/

/-! ## Rényi Entropy -/


end NonArchInfoTheory


