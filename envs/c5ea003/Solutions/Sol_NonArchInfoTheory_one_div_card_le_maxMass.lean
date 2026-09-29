-- Prove2me | solution 1 for NonArchInfoTheory.one_div_card_le_maxMass
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:14:24.471512+00:00
-- url     : https://prove2.me/submissions/c384a574-0553-4357-a2b7-077360a6652d

-- Sol generated from Bridges/MinEntropy.lean
import Mathlib
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_NonArchInfoTheory_mass_le_maxMass
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
theorem solution(μ : FinProbDist α) :
    1 / (Fintype.card α : ℝ) ≤ maxMass μ := by
  have hcard : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  suffices h : 1 ≤ (Fintype.card α : ℝ) * maxMass μ by rwa [div_le_iff₀' hcard]
  calc (1 : ℝ) = ∑ x : α, μ.mass x := μ.mass_sum_one.symm
    _ ≤ ∑ _ : α, maxMass μ := Finset.sum_le_sum (fun x _ => mass_le_maxMass μ x)
    _ = (Fintype.card α : ℝ) * maxMass μ := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
