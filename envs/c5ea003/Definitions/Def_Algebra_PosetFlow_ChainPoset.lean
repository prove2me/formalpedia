-- Prove2me | Definitions.Def_Algebra_PosetFlow_ChainPoset
-- name    : Algebra_PosetFlow_ChainPoset
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:42:37.784291+00:00
-- url     : https://prove2.me/theorems/84e0c2b3-dc2b-4289-8a61-6037407d4acb
-- title:
--   Aether Catalog definitions — Algebra_PosetFlow_ChainPoset
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PosetFlow.ChainPoset`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PosetFlow/ChainPoset.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_PosetFlow_OrderComplexEuler

/-!
# The refinement poset of strictly increasing chains of a poset

This file formalises the combinatorial core of the *chain replacement of a poset
flow*.  For a poset `P` and `x y : P`, the paper considers the poset of strictly
increasing chains from `x` to `y`, ordered by refinement, and takes its simplicial
nerve as the space of execution paths from `x` to `y` of the replacement flow.

Here a chain from `x` to `y` is recorded by its underlying finite set
(`PosetFlow.ChainFrom x y`): a finite, totally ordered subset of `P` containing `x`
and `y` and contained in the interval `[x, y]`.  Refinement is inclusion of
carriers.  We prove:

* `PosetFlow.ChainFrom.bot_le` : the chain `{x, y}` is the least element, so the
  refinement poset is a cone.  This is why the chain replacement of a poset flow is
  a *replacement*: its path spaces are contractible.
* `PosetFlow.alternatingSum_chainFrom_eq_zero` : the Euler-characteristic shadow of
  that contractibility, obtained from `OrderComplexEuler`.
* `PosetFlow.ChainFrom.concat` and `PosetFlow.ChainFrom.concat_assoc` : the
  composition law of the chain replacement (a poset-enriched semicategory
  structure), which is monotone in each variable.
* `PosetFlow.chainSplitOrderIso` : the *unique factorisation* of a chain through an
  intermediate point, as an order isomorphism
  `{E : ChainFrom x z // y ∈ E} ≃o ChainFrom x y × ChainFrom y z`.  This is the
  combinatorial statement which, at the level of flows, says that concatenation
  identifies path spaces of composites.
-/

namespace PosetFlow

open Finset

variable {P : Type*} [PartialOrder P] [DecidableEq P] [DecidableLE P]

/-- A (strictly increasing) chain from `x` to `y` in a poset, recorded by its
underlying finite set: it is totally ordered, contains `x` and `y`, and lies in the
interval `[x, y]`. -/
structure ChainFrom (x y : P) where
  /-- the underlying finite set of the chain -/
  carrier : Finset P
  mem_source : x ∈ carrier
  mem_target : y ∈ carrier
  bounded : ∀ ⦃a⦄, a ∈ carrier → x ≤ a ∧ a ≤ y
  total : ∀ ⦃a⦄, a ∈ carrier → ∀ ⦃b⦄, b ∈ carrier → a ≤ b ∨ b ≤ a

namespace ChainFrom

variable {x y z w : P}

omit [DecidableEq P] [DecidableLE P] in
@[ext] theorem ext {C D : ChainFrom x y} (h : C.carrier = D.carrier) : C = D := by
  cases C; cases D; simp_all

omit [DecidableEq P] [DecidableLE P] in
theorem carrier_injective : Function.Injective (ChainFrom.carrier : ChainFrom x y → Finset P) :=
  fun _ _ h => ext h

/-- Refinement order: a chain is below a chain refining it. -/
instance instPartialOrder : PartialOrder (ChainFrom x y) where
  le C D := C.carrier ⊆ D.carrier
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Finset.Subset.trans h₁ h₂
  le_antisymm _ _ h₁ h₂ := ext (Finset.Subset.antisymm h₁ h₂)

omit [DecidableEq P] [DecidableLE P] in
theorem le_iff {C D : ChainFrom x y} : C ≤ D ↔ C.carrier ⊆ D.carrier := Iff.rfl

instance : DecidableEq (ChainFrom x y) := fun C D =>
  decidable_of_iff (C.carrier = D.carrier) ⟨ext, fun h => h ▸ rfl⟩

instance : DecidableLE (ChainFrom x y) := fun C D =>
  decidable_of_iff (C.carrier ⊆ D.carrier) le_iff.symm

noncomputable instance [Fintype P] : Fintype (ChainFrom x y) :=
  Fintype.ofInjective _ carrier_injective

omit [DecidableEq P] [DecidableLE P] in
/-- A chain from `x` to `y` can only exist when `x ≤ y`. -/
theorem source_le_target (C : ChainFrom x y) : x ≤ y := (C.bounded C.mem_target).1

/-- The coarsest chain from `x` to `y`, namely `{x, y}`. -/
def coarsest (h : x ≤ y) : ChainFrom x y where
  carrier := {x, y}
  mem_source := by simp
  mem_target := by simp
  bounded := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact ⟨le_refl _, h⟩
    · rw [Finset.mem_singleton] at ha; subst ha; exact ⟨h, le_refl _⟩
  total := by
    intro a ha b hb
    have hx : ∀ c ∈ ({x, y} : Finset P), c = x ∨ c = y := by
      intro c hc
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact Or.inl rfl
      · exact Or.inr (Finset.mem_singleton.1 hc)
    rcases hx a ha with rfl | rfl <;> rcases hx b hb with rfl | rfl
    · exact Or.inl (le_refl _)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl (le_refl _)





/-- Concatenation of chains: the composition law of the chain replacement. -/
def concat (C : ChainFrom x y) (D : ChainFrom y z) : ChainFrom x z where
  carrier := C.carrier ∪ D.carrier
  mem_source := Finset.mem_union_left _ C.mem_source
  mem_target := Finset.mem_union_right _ D.mem_target
  bounded := by
    intro a ha
    rcases Finset.mem_union.1 ha with ha | ha
    · exact ⟨(C.bounded ha).1, le_trans (C.bounded ha).2 (D.source_le_target)⟩
    · exact ⟨le_trans C.source_le_target (D.bounded ha).1, (D.bounded ha).2⟩
  total := by
    intro a ha b hb
    rcases Finset.mem_union.1 ha with ha | ha <;> rcases Finset.mem_union.1 hb with hb | hb
    · exact C.total ha hb
    · exact Or.inl (le_trans (C.bounded ha).2 (D.bounded hb).1)
    · exact Or.inr (le_trans (C.bounded hb).2 (D.bounded ha).1)
    · exact D.total ha hb






/-- The initial segment of a chain through an intermediate point `y`. -/
def restrictLeft (E : ChainFrom x z) (hy : y ∈ E.carrier) : ChainFrom x y where
  carrier := E.carrier.filter (· ≤ y)
  mem_source := Finset.mem_filter.2 ⟨E.mem_source, (E.bounded hy).1⟩
  mem_target := Finset.mem_filter.2 ⟨hy, le_refl _⟩
  bounded := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact ⟨(E.bounded ha.1).1, ha.2⟩
  total := by
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact E.total ha.1 hb.1

/-- The terminal segment of a chain through an intermediate point `y`. -/
def restrictRight (E : ChainFrom x z) (hy : y ∈ E.carrier) : ChainFrom y z where
  carrier := E.carrier.filter (y ≤ ·)
  mem_source := Finset.mem_filter.2 ⟨hy, le_refl _⟩
  mem_target := Finset.mem_filter.2 ⟨E.mem_target, (E.bounded hy).2⟩
  bounded := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact ⟨ha.2, (E.bounded ha.1).2⟩
  total := by
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact E.total ha.1 hb.1








end ChainFrom

open ChainFrom




end PosetFlow


