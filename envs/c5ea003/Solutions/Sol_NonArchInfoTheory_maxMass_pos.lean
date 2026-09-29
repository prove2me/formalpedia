-- Prove2me | solution 1 for NonArchInfoTheory.maxMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:58:29.939969+00:00
-- url     : https://prove2.me/submissions/190442cb-0b19-4590-8cf3-20cb359297c4

-- Sol generated from Bridges/MinEntropy.lean
import Mathlib
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_NonArchInfoTheory_mass_le_maxMass
import Theorems.Thm_NonArchInfoTheory_maxMass_exists_witness
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
theorem solution(μ : FinProbDist α) : 0 < maxMass μ := by
  by_contra h; push_neg at h
  have h0 : maxMass μ = 0 := le_antisymm h (by
    obtain ⟨x, hx⟩ := maxMass_exists_witness μ; rw [← hx]; exact μ.mass_nonneg x)
  have : (∑ x : α, μ.mass x) = 0 := Finset.sum_eq_zero fun x _ => by
    linarith [mass_le_maxMass μ x, μ.mass_nonneg x]
  linarith [μ.mass_sum_one]
