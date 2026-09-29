-- Prove2me | Definitions.Def_Bridges_ClosureSheafCodeDuality
-- name    : Bridges_ClosureSheafCodeDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:25:46.855757+00:00
-- url     : https://prove2.me/theorems/296db057-5954-41db-b4d5-8f91ef6be274
-- title:
--   Aether Catalog definitions — Bridges_ClosureSheafCodeDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureSheafCodeDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureSheafCodeDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Closure-Sheaf Code Duality via Cellular Decoder Reconstruction

## Overview

We establish a finite duality between constraint-closure systems on finite cell complexes
and cellular decoder presentations. The main results are:

1. **Reconstruction (Theorem A)**: Every constraint system yields a canonical decoder
   whose codewords are exactly the valid (zero-defect) assignments.
2. **Inverse Reconstruction (Theorem B)**: Every decoder yields a canonical constraint
   system whose valid set contains the original codewords.
3. **Minimality (Theorem C)**: The canonical constraint system induced by a set of
   assignments has the smallest domains among all systems accepting those assignments.
   This is the cellular Myhill–Nerode theorem.
4. **Round-Trip Duality (Theorem D)**: Under a finite gluing axiom, the round-trip
   closure → decoder → closure recovers the original valid set exactly.
5. **Certified Decoder (Theorem E)**: The canonical decoder construction is sound,
   complete, and produces minimal domains via refinement.

## Mathematical Context

This formalizes the "closure-decoder duality": constraint propagation systems (modeling
local physics, CSP, or coding constraints) are equivalent to local decoder presentations.
The defect functional measures failure of local consistency, and minimization via a kernel
congruence gives a cellular Myhill–Nerode theorem. The finite gluing axiom bridges
pairwise local consistency to global codeword reconstruction.
-/

open Set Function Finset Classical

noncomputable section

namespace ClosureSheafCodeDuality

/-! ## Section 1: Finite Cell Complexes -/

/-- A finite cell complex: a finite type with a decidable, reflexive incidence relation. -/
structure CellComplex where
  Cell : Type*
  [cellFintype : Fintype Cell]
  [cellDecEq : DecidableEq Cell]
  Inc : Cell → Cell → Prop
  [incDecRel : DecidableRel Inc]
  inc_refl : ∀ σ, Inc σ σ

attribute [instance] CellComplex.cellFintype CellComplex.cellDecEq CellComplex.incDecRel

namespace CellComplex

variable (K : CellComplex)

/-- The star of a cell: all cells incident to it (including itself). -/
def star (σ : K.Cell) : Finset K.Cell :=
  Finset.univ.filter (K.Inc σ)



end CellComplex

/-! ## Section 2: Constraint Systems -/

variable {K : CellComplex} {Obs : Type*} [Fintype Obs] [DecidableEq Obs]

/-- An assignment of observables to cells. -/
abbrev Assignment (K : CellComplex) (Obs : Type*) := K.Cell → Obs

/-- A constraint system on a cell complex with observables.
    Assigns to each cell a finite domain of admissible values and to each pair
    of incident cells a pairwise compatibility constraint. -/
structure ConstraintSystem (K : CellComplex) (Obs : Type*) [Fintype Obs] [DecidableEq Obs] where
  /-- Local domain: admissible values at each cell -/
  domain : K.Cell → Finset Obs
  /-- Pairwise compatibility constraint on incident cells -/
  compat : K.Cell → K.Cell → Obs → Obs → Prop
  /-- Every domain is nonempty -/
  domainNonempty : ∀ σ, (domain σ).Nonempty

/-- An assignment is valid (zero-defect) if all values are in domains and
    all incident pairs satisfy compatibility. -/
def ConstraintSystem.IsValid (S : ConstraintSystem K Obs) (f : Assignment K Obs) : Prop :=
  (∀ σ, f σ ∈ S.domain σ) ∧
  (∀ σ τ, K.Inc σ τ → S.compat σ τ (f σ) (f τ))

/-- The set of all valid assignments (zero-defect global sections). -/
def ConstraintSystem.ValidSet (S : ConstraintSystem K Obs) : Set (Assignment K Obs) :=
  {f | S.IsValid f}

/-! ## Section 3: Cellular Decoders -/

/-- A cellular decoder: a local check predicate at each cell. -/
structure CellularDecoder (K : CellComplex) (Obs : Type*) where
  /-- Check predicate: whether assignment passes the check at cell σ -/
  check : K.Cell → (K.Cell → Obs) → Prop

/-- Codewords: assignments passing all checks. -/
def CellularDecoder.Codewords (D : CellularDecoder K Obs) : Set (K.Cell → Obs) :=
  {f | ∀ σ, D.check σ f}

/-- Soundness: codewords ⊆ target set. -/
def CellularDecoder.IsSoundFor (D : CellularDecoder K Obs) (W : Set (K.Cell → Obs)) : Prop :=
  D.Codewords ⊆ W

/-- Completeness: target set ⊆ codewords. -/
def CellularDecoder.IsCompleteFor (D : CellularDecoder K Obs) (W : Set (K.Cell → Obs)) : Prop :=
  W ⊆ D.Codewords

/-! ## Section 4: Defect Functional -/

/-- Domain defect at a cell: the value is not in the admissible domain. -/
def domainDefect (S : ConstraintSystem K Obs) (f : Assignment K Obs) (σ : K.Cell) : Prop :=
  f σ ∉ S.domain σ

/-- Compatibility defect at a pair of cells. -/
def compatDefect (S : ConstraintSystem K Obs) (f : Assignment K Obs)
    (σ τ : K.Cell) : Prop :=
  K.Inc σ τ ∧ ¬S.compat σ τ (f σ) (f τ)


/-- The number of domain defects. -/
def domainDefectCount (S : ConstraintSystem K Obs) (f : Assignment K Obs) : ℕ :=
  (Finset.univ.filter (fun σ => f σ ∉ S.domain σ)).card


/-! ## Section 5: Closure Operators -/

/-- A finite closure operator on sets of a type. -/
structure FinClosureOp (α : Type*) where
  cl : Set α → Set α
  extensive : ∀ S, S ⊆ cl S
  monotone : ∀ S T, S ⊆ T → cl S ⊆ cl T
  idempotent : ∀ S, cl (cl S) = cl S


/-- A set is closed iff it is a fixed point of the closure operator. -/
def FinClosureOp.IsClosed {α : Type*} (C : FinClosureOp α) (S : Set α) : Prop :=
  C.cl S = S


/-! ## Section 6: Closure-Cosheaf Systems -/


/-! ## Section 7: Canonical Constructions

The canonical decoder from a constraint system checks domain membership and compatibility.
The canonical constraint system from a set of assignments uses projections as domains
and co-occurrence as compatibility. These are the two directions of the duality. -/

/-- The canonical decoder from a constraint system:
    checks domain membership and pairwise compatibility at each cell. -/
def canonicalDecoder (S : ConstraintSystem K Obs) : CellularDecoder K Obs where
  check σ f := f σ ∈ S.domain σ ∧ ∀ τ, K.Inc σ τ → S.compat σ τ (f σ) (f τ)

/-- The canonical constraint system from a nonempty set of assignments:
    domains are projections, compatibility is co-occurrence in W. -/
def canonicalConstraint (W : Set (Assignment K Obs))
    (hne : W.Nonempty) : ConstraintSystem K Obs where
  domain σ := Finset.univ.filter (fun a => ∃ f ∈ W, f σ = a)
  compat σ τ a b := ∃ f ∈ W, f σ = a ∧ f τ = b
  domainNonempty σ := by
    obtain ⟨f, hf⟩ := hne
    exact ⟨f σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf, rfl⟩⟩

/-! ## Section 8: Core Duality Theorems -/







/-! ## Section 9: Pairwise Consistency and the Finite Gluing Property

The finite gluing property is the cellular analogue of the sheaf gluing condition.
It states that pairwise consistency (each pair of incident values co-occurs in some
valid assignment) implies global validity. Under this axiom, the round-trip
reconstruction is exact. -/

/-- An assignment is pairwise consistent if each value and each incident pair
    co-occurs with some valid assignment. -/
def PairwiseConsistent (S : ConstraintSystem K Obs) (f : Assignment K Obs) : Prop :=
  (∀ σ, ∃ g ∈ S.ValidSet, g σ = f σ) ∧
  (∀ σ τ, K.Inc σ τ → ∃ g ∈ S.ValidSet, g σ = f σ ∧ g τ = f τ)

/-- The finite gluing property: pairwise consistency implies global validity. -/
def ConstraintSystem.FiniteGluing (S : ConstraintSystem K Obs) : Prop :=
  ∀ f, PairwiseConsistent S f → S.IsValid f



/-! ## Section 10: Extensibility and Domain Recovery -/

/-- A constraint system is extensible if every domain value extends to a valid assignment.
    This means every local state is *reachable* — it participates in some global solution. -/
def ConstraintSystem.Extensible (S : ConstraintSystem K Obs) : Prop :=
  ∀ σ, ∀ a ∈ S.domain σ, ∃ f ∈ S.ValidSet, f σ = a


/-! ## Section 11: Kernel Congruence (Cellular Myhill–Nerode)

The zero-defect kernel congruence identifies observables that behave identically
in all valid assignments. The quotient by this congruence gives the minimal
state space — the cellular analogue of the Myhill–Nerode theorem for automata. -/

/-- Two observables are zero-defect equivalent at cell σ if swapping them in any
    valid assignment preserves validity in both directions. -/
def ZeroDefectEquiv (S : ConstraintSystem K Obs) (σ : K.Cell) (a b : Obs) : Prop :=
  a ∈ S.domain σ ∧ b ∈ S.domain σ ∧
  (∀ f, S.IsValid f → f σ = a → S.IsValid (Function.update f σ b)) ∧
  (∀ f, S.IsValid f → f σ = b → S.IsValid (Function.update f σ a))



/-- The reachable values at cell σ: values appearing in some valid assignment. -/
def reachableValues (S : ConstraintSystem K Obs) (σ : K.Cell) : Set Obs :=
  {a | ∃ f ∈ S.ValidSet, f σ = a}



/-! ## Section 12: Codeword Equivalence -/

/-- Two constraint systems are codeword-equivalent if they have the same valid set. -/
def ConstraintSystem.CodewordEquiv (S₁ S₂ : ConstraintSystem K Obs) : Prop :=
  S₁.ValidSet = S₂.ValidSet



/-! ## Section 13: Certified Decoder -/



/-! ## Section 14: Zero-Defect Sections Equal Codewords -/

/-- Global zero-defect sections: assignments satisfying all local constraints. -/
def GlobalZeroDefectSections (S : ConstraintSystem K Obs) : Set (Assignment K Obs) :=
  {f | ∀ σ, f σ ∈ S.domain σ ∧ ∀ τ, K.Inc σ τ → S.compat σ τ (f σ) (f τ)}



/-! ## Section 15: Refinement to Reachable States

The refinement operator projects a constraint system down to its reachable states:
domain values that actually appear in valid assignments. This is the algorithmic
core of the Myhill–Nerode minimization. -/

/-- Refine a constraint system to reachable values only:
    keep only domain elements that appear in some valid assignment. -/
def refineToReachable (S : ConstraintSystem K Obs)
    (hne : S.ValidSet.Nonempty) : ConstraintSystem K Obs where
  domain σ := (S.domain σ).filter (fun a => ∃ f ∈ S.ValidSet, f σ = a)
  compat := S.compat
  domainNonempty σ := by
    obtain ⟨f, hf⟩ := hne
    exact ⟨f σ, Finset.mem_filter.mpr ⟨hf.1 σ, f, hf, rfl⟩⟩






/-! ## Section 16: Main Duality Theorem -/



/-! ## Section 17: Defect Preservation -/



/-! ## Section 18: Concrete Example — Path Graph Repetition Code -/

/-- A path graph on `Fin n`: cell `i` is incident to cell `j` if `|i - j| ≤ 1`. -/
def pathGraph (n : ℕ) (_hn : 0 < n) : CellComplex where
  Cell := Fin n
  Inc i j := (i : ℕ) = j ∨ (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
  incDecRel := inferInstance
  inc_refl _ := Or.inl rfl

/-- The repetition code on a path graph: all cells must have the same value.
    Compatibility requires equal values at incident cells. -/
def repetitionCode (n : ℕ) (hn : 0 < n) : ConstraintSystem (pathGraph n hn) Bool where
  domain _ := Finset.univ
  compat _ _ a b := a = b
  domainNonempty _ := ⟨true, Finset.mem_univ _⟩





end ClosureSheafCodeDuality


