-- Prove2me | Definitions.Def_Bridges_Foundations
-- name    : Bridges_Foundations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:37.829548+00:00
-- url     : https://prove2.me/theorems/fa360414-8ba2-496e-a661-e108e9fd5c18
-- title:
--   Aether Catalog definitions — Bridges_Foundations
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.Foundations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/Foundations.lean by skeleton subtraction
import Mathlib

/-! # Topos-Theoretic Machine Learning: Foundations

This file formalizes the algebraic and combinatorial foundations connecting
topos theory to statistical learning theory. We define concrete structures
for concept classes, VC dimension (as a shattering invariant), sample complexity
bounds, and presheaf-based hypothesis spaces.

## Main Structures and Definitions
* `ConceptFamily` — A family of subsets representing learnable concepts
* `shatters` — Predicate: a concept family shatters a set S
* `vcDimBound` — VC dimension as maximal cardinality of shattered sets
* `SieveOn` — Sieve structure encoding concept hierarchies
* `CompactRank` — Compact subobject rank bounding learnability
* `TransferMorphism` — Morphism between concept families preserving learnability
* `LipschitzTransfer` — Transfer with Lipschitz-certified sample complexity inflation

## Bridge: connects Category Theory (presheaves, sieves, subobject classifiers) →
   Statistical Learning Theory (VC dimension, PAC learning, sample complexity) →
   Cryptography (lattice hardness via non-compact rank) →
   Quantum Information (dagger-symmetric concept duality)
-/

noncomputable section

open Finset Real

/-! ## I. Concept Families and Shattering

A concept family over a universe `α` is a collection of subsets.
The VC dimension measures the largest set that can be shattered. -/

/-- `ConceptFamily α`: A family of subsets of `α`, representing a hypothesis class.
    Each concept `c : Set α` classifies points as positive or negative.
    Bridge: connects combinatorics (set families) to ML (hypothesis classes). -/
structure ConceptFamily (α : Type*) where
  /-- The collection of concepts -/
  concepts : Set (Set α)
  /-- The family is nonempty -/
  nonempty : concepts.Nonempty

/-- A concept family `C` shatters a finite set `S` if for every subset `T ⊆ S`,
    there exists a concept `c ∈ C` such that `c ∩ S = T`.
    This is the combinatorial core of VC theory.
    Bridge: connects combinatorics (set intersection) to ML (realizability). -/
def ConceptFamily.shatters {α : Type*} (C : ConceptFamily α) (S : Finset α) : Prop :=
  ∀ T : Finset α, T ⊆ S → ∃ c ∈ C.concepts, ∀ x ∈ S, (x ∈ c ↔ x ∈ T)

/-- The VC dimension of a concept family: bounded by `d` means no set of
    size exceeding `d` is shattered.
    Bridge: connects combinatorics to learning theory — this invariant controls
    sample complexity and is the topos-theoretic compact subobject rank. -/
def ConceptFamily.vcDimBound {α : Type*} (C : ConceptFamily α) (d : ℕ) : Prop :=
  ∀ S : Finset α, C.shatters S → S.card ≤ d

/-- A concept family has finite VC dimension `d` if `d` is the least bound. -/
def ConceptFamily.hasVCDim {α : Type*} (C : ConceptFamily α) (d : ℕ) : Prop :=
  C.vcDimBound d ∧ (d = 0 ∨ ∃ S : Finset α, C.shatters S ∧ S.card = d)

/-! ## II. Sauer-Shelah Growth Function

The growth function `Π_C(m)` counts the maximum number of distinct labelings
a concept family can induce on `m` points. The Sauer-Shelah lemma bounds this. -/

/-- The Sauer-Shelah polynomial bound: `∑_{i=0}^{d} C(m, i)`.
    This bounds the growth function of any concept family with VC dimension d.
    Bridge: connects combinatorics (binomial sums) to ML (growth function). -/
def sauerShelahBound (m d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d + 1), m.choose i





/-! ## III. Presheaf Hypothesis Structures

We model the hypothesis topos `[D^op, Set]` concretely:
data objects are elements of a finite type, and presheaves assign
sets of hypotheses to each data object. -/

/-- `SieveOn α d`: A sieve on data object `d` in a universe `α` equipped
    with a preorder. Sieves are downward-closed sets of morphisms,
    encoding concept hierarchies in the subobject classifier Ω_D.
    Bridge: connects category theory (sieves) to ML (concept hierarchies). -/
structure SieveOn (α : Type*) [Preorder α] (d : α) where
  /-- The carrier set of the sieve -/
  carrier : Set α
  /-- Sieves are downward-closed -/
  downward_closed : ∀ x y, x ∈ carrier → y ≤ x → y ∈ carrier
  /-- Elements are below the target -/
  below_target : ∀ x ∈ carrier, x ≤ d

/-- The set of sieves on `d` forms a partial order, modeling the
    subobject classifier value `Ω_D(d)` in the hypothesis topos.
    Bridge: connects topos theory (Ω values) to lattice theory. -/
instance SieveOn.instPartialOrder {α : Type*} [Preorder α] {d : α} :
    PartialOrder (SieveOn α d) where
  le s₁ s₂ := s₁.carrier ⊆ s₂.carrier
  le_refl s := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂
  le_antisymm s₁ s₂ h₁ h₂ := by
    cases s₁; cases s₂; simp only [mk.injEq]
    exact Set.Subset.antisymm h₁ h₂

/-- The maximal sieve: all morphisms into `d`.
    Corresponds to the "true" truth value in the subobject classifier. -/
def SieveOn.maximal {α : Type*} [Preorder α] (d : α) : SieveOn α d where
  carrier := {x | x ≤ d}
  downward_closed := fun _ _ hx hy => le_trans hy hx
  below_target := fun _ hx => hx

/-- The empty sieve: no morphisms.
    Corresponds to the "false" truth value in the subobject classifier. -/
def SieveOn.empty {α : Type*} [Preorder α] (d : α) : SieveOn α d where
  carrier := ∅
  downward_closed := fun _ _ hx _ => absurd hx (by simp)
  below_target := fun _ hx => absurd hx (by simp)



/-! ## IV. Compact Subobject Rank

The compact subobject rank is the topos-theoretic invariant that
equals the VC dimension. We define it combinatorially. -/

/-- `CompactRank`: The compact subobject rank of a concept family,
    defined as the maximal size of a set that can be shattered.
    In the hypothesis topos, this equals the categorical compactness rank.
    Bridge: connects category theory (compact objects) to ML (VC dimension). -/
def CompactRank {α : Type*} (C : ConceptFamily α) (n : ℕ) : Prop :=
  C.vcDimBound n ∧ (n = 0 ∨ ∃ S : Finset α, C.shatters S ∧ S.card = n)


/-! ## V. Sample Complexity Bounds

The fundamental theorem of statistical learning connects VC dimension
to sample complexity via explicit quantitative bounds. -/

/-- Sample complexity bound: `c · d / ε² · log(1/δ)` samples suffice
    for PAC learning a concept family with VC dimension d.
    Bridge: connects learning theory to analysis (logarithmic bounds). -/
def sampleComplexityBound (d : ℕ) (ε δ : ℝ) : ℝ :=
  37 * d / ε ^ 2 * Real.log (1 / δ)



/-! ## VI. Transfer Morphisms

A transfer morphism between concept families models the inverse image
functor of a geometric morphism between hypothesis toposes. -/

/-- `TransferMorphism`: A structure-preserving map between concept families,
    modeling the inverse image functor f* of a geometric morphism
    f : Hyp(D₁) → Hyp(D₂) between hypothesis toposes.
    Bridge: connects category theory (geometric morphisms) to ML (transfer learning)
    to cryptography (lattice-based transfer for post_quantum_security). -/
structure TransferMorphism {α β : Type*} (C₁ : ConceptFamily α) (C₂ : ConceptFamily β) where
  /-- The underlying map on universes -/
  mapPoint : α → β
  /-- Concepts are pulled back: f*(c₂) = {x | f(x) ∈ c₂} -/
  conceptPullback : ∀ c ∈ C₂.concepts, (Set.preimage mapPoint c) ∈ C₁.concepts
  /-- The Lipschitz constant of the transfer (sample complexity inflation factor) -/
  lipschitzConst : ℝ
  /-- The Lipschitz constant is at least 1 -/
  lipschitz_ge_one : 1 ≤ lipschitzConst


/-! ## VII. Lattice Crypto Hardness Structure

Non-compact subobjects yield cryptographic hardness:
concept families with high VC dimension require exponentially many samples. -/

/-- `CryptoHardnessWitness`: Certificate that a concept family has
    VC dimension exceeding a threshold, implying Ω(2^k) sample complexity.
    Bridge: connects topos theory (non-compact rank) to cryptography
    (lattice hardness, post_quantum_security). -/
structure CryptoHardnessWitness {α : Type*} (C : ConceptFamily α) (k : ℕ) where
  /-- A shattered set witnessing high VC dimension -/
  witness : Finset α
  /-- The witness has the required size -/
  witness_card : witness.card = k
  /-- The witness is shattered -/
  witness_shattered : C.shatters witness

end


