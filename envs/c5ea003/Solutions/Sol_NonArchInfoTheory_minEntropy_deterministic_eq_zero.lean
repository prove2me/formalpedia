-- Prove2me | solution 1 for NonArchInfoTheory.minEntropy_deterministic_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:14:24.034736+00:00
-- url     : https://prove2.me/submissions/73460c9f-814c-4dd2-94dc-733924c6506a

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


/-- The max mass of a deterministic distribution is 1. -/
theorem deterministicDist_maxMass [DecidableEq α] (a : α) :
    maxMass (deterministicDist a) = 1 := by
  unfold maxMass deterministicDist; simp only
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun x _ => by split_ifs <;> linarith)
  · calc (1 : ℝ) = (fun (x : α) => if x = a then (1 : ℝ) else 0) a := by simp
      _ ≤ _ := Finset.le_sup' (fun (x : α) => if x = a then (1 : ℝ) else 0)
                  (Finset.mem_univ a)


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
theorem solution[DecidableEq α] (a : α) :
    minEntropy (deterministicDist a) = 0 := by
  unfold minEntropy; rw [deterministicDist_maxMass, Real.log_one, neg_zero]
