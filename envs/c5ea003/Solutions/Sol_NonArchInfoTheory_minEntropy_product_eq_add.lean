-- Prove2me | solution 1 for NonArchInfoTheory.minEntropy_product_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:17:10.351894+00:00
-- url     : https://prove2.me/submissions/a86fed63-0039-4edd-9fd0-53e0a62e1a0e

-- Sol generated from Bridges/MinEntropy.lean
import Mathlib
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_NonArchInfoTheory_maxMass_pos
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

open NonArchInfoTheory


variable {α : Type*} [Fintype α]



/-! ## Total Variation Distance

These results don't require `Nonempty α`, so we prove them before
introducing that variable. -/


variable {α : Type*} [Fintype α]








/-! ## Uniform Distribution -/




/-! ## Maximum Mass -/

variable [Nonempty α]







/-! ## Min-Entropy Definition and Properties -/




/-! ## Deterministic Distribution -/




/-! ## Uniform Distribution Entropy -/



/-! ## Product Distribution -/

variable {β : Type*} [Fintype β] [Nonempty β]


/-
Key lemma: max of product of nonneg functions = product of maxes.
    Bridge: tropical ⊗ distributes over product spaces.
-/
theorem sup'_product_eq_mul_sup'
    (f : α → ℝ) (g : β → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y) :
    Finset.sup' Finset.univ Finset.univ_nonempty (fun p : α × β => f p.1 * g p.2) =
    Finset.sup' Finset.univ Finset.univ_nonempty f *
    Finset.sup' Finset.univ Finset.univ_nonempty g := by
  refine' le_antisymm _ _;
  · simp +decide [ Finset.sup'_le_iff ];
    exact fun a b => mul_le_mul ( Finset.le_sup' ( fun x => f x ) ( Finset.mem_univ a ) ) ( Finset.le_sup' ( fun x => g x ) ( Finset.mem_univ b ) ) ( hg b ) ( by exact le_trans ( hf a ) ( Finset.le_sup' ( fun x => f x ) ( Finset.mem_univ a ) ) );
  · simp +decide [ Finset.sup'_le_iff ];
    rcases Finset.exists_mem_eq_sup' ( Finset.univ_nonempty ) f with ⟨ a, ha ⟩ ; rcases Finset.exists_mem_eq_sup' ( Finset.univ_nonempty ) g with ⟨ b, hb ⟩ ; use a, b ; aesop;

/-- Max mass of product = product of max masses.
    Impact: post_quantum_security — joint security decomposes multiplicatively. -/
theorem productDist_maxMass (μ : FinProbDist α) (ν : FinProbDist β) :
    maxMass (productDist μ ν) = maxMass μ * maxMass ν := by
  unfold maxMass productDist; simp only
  exact sup'_product_eq_mul_sup' μ.mass ν.mass μ.mass_nonneg ν.mass_nonneg


/-! ## Exp-Entropy Identity -/



/-! ## Min-Entropy Characterization -/



/-! ## Tropical Valuation -/



/-! ## Idempotent Entropy Axioms -/


/-! ## Marginal Distributions -/



/-! ## Bernoulli Distribution -/


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



open NonArchInfoTheory in
theorem solution(μ : FinProbDist α) (ν : FinProbDist β) :
    minEntropy (productDist μ ν) = minEntropy μ + minEntropy ν := by
  unfold minEntropy; rw [productDist_maxMass]
  rw [Real.log_mul (ne_of_gt (maxMass_pos μ)) (ne_of_gt (maxMass_pos ν))]; ring
