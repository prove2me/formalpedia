-- Prove2me | Definitions.Def_Logic_StoneDualityNeuralNetworks
-- name    : Logic_StoneDualityNeuralNetworks
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:29:33.765161+00:00
-- url     : https://prove2.me/theorems/b009e19a-3bc1-40e3-9111-f6527587df85
-- title:
--   Aether Catalog definitions — Logic_StoneDualityNeuralNetworks
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.StoneDualityNeuralNetworks`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/StoneDualityNeuralNetworks.lean by skeleton subtraction
import Mathlib

/-!
# Stone duality and neural classifiers: precise positive results and counterexamples

A classifier induces a Boolean algebra of observable predicates, but several stronger
claims in the proposed framing fail.  This file isolates the failures without assuming
any particular implementation of neural networks.
-/

namespace StoneDualityNeuralNetworks

/-- The strict-threshold binary classifier on the real line. -/
noncomputable def thresholdClassifier (x : ℝ) : Bool := decide (0 < x)

/-- Its positive decision region. -/
def positiveRegion : Set ℝ := {x | thresholdClassifier x = true}

/-- Its nonpositive decision region. -/
def nonpositiveRegion : Set ℝ := {x | thresholdClassifier x = false}



/-- Activation vector of a list of scalar threshold neurons. -/
noncomputable def activationVector {k : ℕ} (bias : Fin k → ℝ) (x : ℝ) : Fin k → Bool :=
  fun i => decide (bias i < x)




/-- A hypothesis class is a set of subsets, viewed as positive regions. -/
abbrev HypothesisClass (α : Type*) := Set (Set α)

/-- Standard finite-set shattering. -/
def Shatters {α : Type*} (H : HypothesisClass α) (C : Finset α) : Prop :=
  ∀ L : Finset α, L ⊆ C → ∃ h ∈ H, (C : Set α) ∩ h = L




/-- Pullback of a set along any map; this is the correct elementary mechanism by which
clopens of a finite discrete pattern space yield classifier predicates. -/
def pullback {α β : Type*} (encode : α → β) (s : Set β) : Set α := encode ⁻¹' s




end StoneDualityNeuralNetworks


