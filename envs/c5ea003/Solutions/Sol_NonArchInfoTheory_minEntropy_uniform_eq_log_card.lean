-- Prove2me | solution 1 for NonArchInfoTheory.minEntropy_uniform_eq_log_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:08:32.954701+00:00
-- url     : https://prove2.me/submissions/ca98f446-eb43-47e0-880a-6ed810107db9

-- Sol generated from Bridges/MinEntropy.lean
import Mathlib
import Definitions.Def_Bridges_MinEntropy
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

/-- Max mass of the uniform distribution is 1/|α|. -/
theorem uniformDist_maxMass :
    maxMass (uniformDist α) = 1 / (Fintype.card α : ℝ) := by
  unfold maxMass uniformDist; simp only
  exact Finset.sup'_eq_of_forall _ _ (fun _ _ => rfl)


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
theorem solution:
    minEntropy (uniformDist α) = Real.log (Fintype.card α : ℝ) := by
  unfold minEntropy; rw [uniformDist_maxMass]
  have hcard : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  rw [Real.log_div (by linarith) (by linarith), Real.log_one]; ring
