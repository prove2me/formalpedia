-- Prove2me | Definitions.Def_Logic_PosetTheory_TemporalStoneDuality
-- name    : Logic_PosetTheory_TemporalStoneDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:02:34.878615+00:00
-- url     : https://prove2.me/theorems/16e9cec9-52cd-451a-85cd-b06c31c23ff0
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_TemporalStoneDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.TemporalStoneDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/TemporalStoneDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Temporal Stone Duality from Idempotent Semiring Fixpoints

This file establishes a bridge between temporal specification, fixpoint
semantics, and finite Stone/Birkhoff duality in an idempotent algebraic setting.

## Main results

* `boxPred` — the monotone universal temporal predecessor operator
* `diamondPred` — the monotone existential temporal predecessor operator
* `boxPred_inter` — □ distributes over intersection
* `finite_gfp_stabilizes` — finite iteration stabilizes the greatest fixpoint
* `TFormula.satDecidable` — model checking for temporal formulas is decidable
* `temporal_duality_equiv` — behavioral equivalence = equal dual points
* `boxPred_fixpoints_complete_lattice` — fixpoints of □ form a complete lattice
* `finite_fixpoint_lattice` — fixpoints of □ are finite for finite state spaces
* `definablePredicates_boolean_subalgebra` — definable predicates form a Boolean algebra

## Overview

For a finite state transition system `step : α → Finset α`, we define:
- A temporal formula language with atoms, boolean connectives, and □/◇
- Semantics `sat` interpreting formulas as predicates on states
- The monotone box operator `boxPred step` on `Set α`
- Greatest fixpoint invariant computation via descending Kleene iteration
- Behavioral equivalence and dual theories

We prove that safety model checking reduces to greatest fixpoint computation,
that this computation terminates in finitely many steps, and that behavioral
equivalence under the temporal language is characterized by equality of
dual-space points (theories).
-/


open Set Finset Function

/-! ## The Box and Diamond Operators -/

/-- The universal temporal predecessor: `boxPred step X` is the set of states
    all of whose successors lie in `X`. This is the semantic interpretation of □. -/
def boxPred {α : Type*} [DecidableEq α] (step : α → Finset α) : Set α →o Set α where
  toFun := fun X => {s | ∀ t, t ∈ step s → t ∈ X}
  monotone' := fun _ _ hXY _ hs t ht => hXY (hs t ht)

/-- The existential temporal predecessor: `diamondPred step X` is the set of states
    that have at least one successor in `X`. This is the semantic interpretation of ◇. -/
def diamondPred {α : Type*} [DecidableEq α] (step : α → Finset α) : Set α →o Set α where
  toFun := fun X => {s | ∃ t, t ∈ step s ∧ t ∈ X}
  monotone' := fun _ _ hXY _ ⟨t, ht1, ht2⟩ => ⟨t, ht1, hXY ht2⟩

/-! ## Basic Properties of boxPred -/






/-! ## Temporal Formula Syntax and Semantics -/

/-- Temporal formulas over atomic propositions indexed by `String`. -/
inductive TFormula : Type where
  | atom : String → TFormula
  | top : TFormula
  | bot : TFormula
  | neg : TFormula → TFormula
  | conj : TFormula → TFormula → TFormula
  | disj : TFormula → TFormula → TFormula
  | box : TFormula → TFormula
  | diamond : TFormula → TFormula
  deriving DecidableEq, Repr

/-- Satisfaction relation: `sat step V s φ` means state `s` satisfies formula `φ`
    under transition system `step` and valuation `V`. -/
noncomputable def TFormula.sat {α : Type*} [DecidableEq α]
    (step : α → Finset α) (V : String → Set α) (s : α) : TFormula → Prop
  | .atom p => s ∈ V p
  | .top => True
  | .bot => False
  | .neg φ => ¬ sat step V s φ
  | .conj φ ψ => sat step V s φ ∧ sat step V s ψ
  | .disj φ ψ => sat step V s φ ∨ sat step V s ψ
  | .box φ => ∀ t, t ∈ step s → sat step V t φ
  | .diamond φ => ∃ t, t ∈ step s ∧ sat step V t φ

/-- The semantic extension of a formula: the set of all satisfying states. -/
noncomputable def TFormula.semExt {α : Type*} [DecidableEq α]
    (step : α → Finset α) (V : String → Set α) (φ : TFormula) : Set α :=
  {s | TFormula.sat step V s φ}

/-- The theory of a state: the set of all formulas it satisfies. -/
noncomputable def TFormula.theory {α : Type*} [DecidableEq α]
    (step : α → Finset α) (V : String → Set α) (s : α) : Set TFormula :=
  {φ | TFormula.sat step V s φ}

/-- Behavioral equivalence: two states satisfy exactly the same formulas. -/
noncomputable def TFormula.behavEquiv {α : Type*} [DecidableEq α]
    (step : α → Finset α) (V : String → Set α) (s t : α) : Prop :=
  ∀ φ : TFormula, TFormula.sat step V s φ ↔ TFormula.sat step V t φ




/-! ## Decidability of Satisfaction -/

/-- Satisfaction of temporal formulas is decidable for finite types with
    decidable valuations (using classical logic). -/
noncomputable instance TFormula.satDecidable {α : Type*} [Fintype α] [DecidableEq α]
    (step : α → Finset α) (V : String → Set α)
    (s : α) (φ : TFormula) : Decidable (TFormula.sat step V s φ) :=
  Classical.dec _

/-! ## Greatest Fixpoint Iteration and Stabilization -/

/-- Iterated application of `P ∩ boxPred step (·)`, starting from P.
    This computes the descending Kleene chain for the greatest fixpoint of
    `fun X => P ∩ boxPred step X`. -/
noncomputable def gfpIter {α : Type*} [DecidableEq α] (step : α → Finset α)
    (P : Set α) : ℕ → Set α
  | 0 => P
  | n + 1 => P ∩ boxPred step (gfpIter step P n)


/-- The monotone operator for computing greatest fixpoint of safety invariance. -/
def safetyOp {α : Type*} [DecidableEq α] (step : α → Finset α) (P : Set α) :
    Set α →o Set α where
  toFun X := P ∩ boxPred step X
  monotone' := fun _ _ hXY => Set.inter_subset_inter_right _ ((boxPred step).monotone' hXY)

/-
In a finite type, the descending chain `gfpIter` stabilizes.
-/

/-! ## Finite Lattice of Definable Predicates -/

/-- The set of all semantically definable predicates under a given transition system
    and valuation. -/
noncomputable def definablePredicates {α : Type*} [DecidableEq α]
    (step : α → Finset α) (V : String → Set α) : Set (Set α) :=
  Set.range (TFormula.semExt step V)








/-! ## Behavioral Equivalence and Dual Theories -/




/-! ## The Dual Point Map -/

/-- The dual point map: sends a state to the set of definable predicates containing it.
    This is the finite analogue of the Stone space point associated to a state. -/
noncomputable def dualPoint {α : Type*} [Fintype α] [DecidableEq α]
    (step : α → Finset α) (V : String → Set α) (s : α) : Set (Set α) :=
  {X ∈ definablePredicates step V | s ∈ X}


/-! ## Main Duality Theorem -/


/-! ## Boolean Subalgebra Structure -/


/-! ## Fixpoint Lattice Structure -/

/-- The fixpoints of boxPred on `Set α` form a complete lattice
    (via the Knaster–Tarski theorem). -/
noncomputable instance boxPred_fixpoints_complete_lattice {α : Type*} [Fintype α] [DecidableEq α]
    (step : α → Finset α) :
    CompleteLattice (Function.fixedPoints (boxPred step)) :=
  inferInstance


