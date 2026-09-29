-- Prove2me | Definitions.Def_Bridges_ToposTheoreticML_Foundations
-- name    : Bridges_ToposTheoreticML_Foundations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:26:21.399438+00:00
-- url     : https://prove2.me/theorems/1b78eb3b-0fef-4ffb-8923-8bc66b85dc76
-- title:
--   Aether Catalog definitions — Bridges_ToposTheoreticML_Foundations
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ToposTheoreticML.Foundations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ToposTheoreticML/Foundations.lean by skeleton subtraction
import Mathlib

/-! # Topos-Theoretic Machine Learning: Foundations

This file develops the shared vocabulary connecting statistical learning theory to
topos-theoretic geometry.  It introduces concept families and their shattering /
Vapnik–Chervonenkis dimension, the Sauer–Shelah growth function, an abstract
sample-complexity functional, sieves on a preorder together with their lattice
structure, and the auxiliary data (cryptographic hardness witnesses, transfer
morphisms) used to phrase transfer and lower-bound results.

The downstream file `Bridges/VCCompactness.lean` builds the actual bridge theorems
on top of these definitions.
-/

open Finset

/-! ## Concept families, shattering and VC dimension -/

/-- A **concept family** on `α` is a nonempty collection of subsets of `α`
(the *concepts*), presented by their membership predicate `mem`. -/
structure ConceptFamily (α : Type*) where
  /-- `mem c` holds when `c` is one of the concepts of the family. -/
  mem : Set α → Prop
  /-- A concept family contains at least one concept. -/
  nonempty : ∃ c, mem c

namespace ConceptFamily

variable {α : Type*}

/-- A finite set `S` is **shattered** by the family if every subset `T ⊆ S` is cut
out on `S` by some concept: there is a concept `c` with `c ∩ S = T`. -/
def shatters (C : ConceptFamily α) (S : Finset α) : Prop :=
  ∀ T ⊆ S, ∃ c, C.mem c ∧ ∀ x ∈ S, (x ∈ c ↔ x ∈ T)

/-- `C.vcDimBound d` states that the VC dimension of `C` is at most `d`: no set of
cardinality exceeding `d` is shattered. -/
def vcDimBound (C : ConceptFamily α) (d : ℕ) : Prop :=
  ∀ S : Finset α, C.shatters S → S.card ≤ d

end ConceptFamily

/-- `CompactRank C n` records that `n` is the *compact rank* of the family `C`:
it bounds every shattered set and is either `0` or attained by some shattered set.
This is the learning-theoretic incarnation of a compact subobject rank. -/
def CompactRank {α : Type*} (C : ConceptFamily α) (n : ℕ) : Prop :=
  (∀ S : Finset α, C.shatters S → S.card ≤ n) ∧
    (n = 0 ∨ ∃ S : Finset α, C.shatters S ∧ S.card = n)

/-- A **cryptographic hardness witness** at level `k`: a shattered set of exactly
`k` points, certifying that learning the family is at least as hard as
distinguishing all `2^k` labelings of those points. -/
structure CryptoHardnessWitness {α : Type*} (C : ConceptFamily α) (k : ℕ) where
  /-- The shattered witness set. -/
  witness : Finset α
  /-- The witness set is shattered by the family. -/
  witness_shattered : C.shatters witness
  /-- The witness set has exactly `k` elements. -/
  witness_card : witness.card = k

/-! ## The Sauer–Shelah growth function -/

/-- The **Sauer–Shelah bound** `∑_{i ≤ d} C(m, i)`, the maximal number of distinct
labelings a family of VC dimension `d` can realize on `m` points. -/
def sauerShelahBound (m d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d + 1), m.choose i


/-! ## Sample complexity -/

/-- An abstract **sample-complexity functional** `d / ε² · log(1/δ)`, capturing the
standard dependence on VC dimension `d`, accuracy `ε`, and confidence `δ`. -/
noncomputable def sampleComplexityBound (d : ℕ) (ε δ : ℝ) : ℝ :=
  (d : ℝ) / ε ^ 2 * Real.log (1 / δ)



/-! ## Sieves on a preorder and their lattice structure -/

/-- A **sieve on `d`** in a preorder `α`: a downward-closed set of elements, all of
which lie below the target `d`.  Sieves are the topos-theoretic classifiers used to
encode downward-closed concepts. -/
structure SieveOn (α : Type*) [Preorder α] (d : α) where
  /-- The underlying set of the sieve. -/
  carrier : Set α
  /-- Sieves are closed downward under the order. -/
  downward_closed : ∀ x y, x ∈ carrier → y ≤ x → y ∈ carrier
  /-- Every element of a sieve lies below the target. -/
  below_target : ∀ x, x ∈ carrier → x ≤ d

namespace SieveOn

variable {α : Type*} [Preorder α] {d : α}


/-- Sieves on `d` form a partial order under inclusion of carriers. -/
instance : PartialOrder (SieveOn α d) where
  le s t := s.carrier ⊆ t.carrier
  le_refl _ := subset_rfl
  le_trans _ _ _ h1 h2 := subset_trans h1 h2
  le_antisymm a b h1 h2 := by
    cases a with
    | mk ca _ _ =>
      cases b with
      | mk cb _ _ =>
        have hc : ca = cb := Set.Subset.antisymm h1 h2
        subst hc
        rfl

/-- The empty sieve. -/
def empty (d : α) : SieveOn α d where
  carrier := ∅
  downward_closed := by intro _ _ hx _; exact absurd hx (by simp)
  below_target := by intro _ hx; exact absurd hx (by simp)

/-- The maximal sieve on `d`, consisting of everything below `d`. -/
def maximal (d : α) : SieveOn α d where
  carrier := {x | x ≤ d}
  downward_closed := fun _ _ hx hle => le_trans hle hx
  below_target := fun _ hx => hx



end SieveOn

/-! ## Transfer morphisms -/

/-- A **transfer morphism** between concept families records the Lipschitz constant
governing how accuracy inflates when transporting a learner from one family to
another. -/
structure TransferMorphism {α β : Type*} (C₁ : ConceptFamily α)
    (C₂ : ConceptFamily β) where
  /-- The Lipschitz constant of the transfer map. -/
  lipschitzConst : ℝ


