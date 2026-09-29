-- Prove2me | Definitions.Def_Bridges_ClosureCircuitDuality
-- name    : Bridges_ClosureCircuitDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:35.570052+00:00
-- url     : https://prove2.me/theorems/eed1ca18-44fe-4538-97ba-19e354015dd5
-- title:
--   Aether Catalog definitions — Bridges_ClosureCircuitDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureCircuitDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureCircuitDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Closure-Circuit Duality Project. All rights reserved.

# Closure-Circuit Duality: Certified Monotone Circuit Reconstruction

This file formalizes a duality between finite closure systems and monotone Boolean
circuits, establishing that every closure operator on a finite type admits a unique
canonical residual basis of minimal generators, and that this basis yields a
monotone DNF circuit that correctly computes the closure.

## Main Results

* `generatedClosure_isClosureOperator` — Implication-generated closures are closure operators
* `minimal_support_exists` — Every element in a closure has a minimal support set
* `closure_iff_contains_minimal_support` — Closure membership ↔ existence of a minimal support
* `canonical_basis_is_basis` — The canonical basis satisfies the basis property
* `canonical_basis_unique` — The canonical residual basis is unique
* `reconstructed_circuit_correct` — The reconstructed DNF circuit correctly computes closure
* `finite_closure_duality` — Main duality theorem packaging all results
* `closure_basis_canonical` — Existence and uniqueness of the canonical basis (`∃!`)

## Overview

The central idea is a **Myhill–Nerode-type minimization principle for monotone closure
computation**: bounded dependency rank forces a canonical finite residual basis, and this
basis is exactly the algebraic shadow of a minimal monotone circuit.
-/


namespace ClosureCircuitDuality

open Set Finset

noncomputable section

/-! ## Part 1: Core Definitions -/

/-- A closure operator on `Set α`: extensive, monotone, and idempotent. -/
structure IsClosureOperator {α : Type*} (cl : Set α → Set α) : Prop where
  extensive : ∀ s, s ⊆ cl s
  monotone : ∀ ⦃s t⦄, s ⊆ t → cl s ⊆ cl t
  idempotent : ∀ s, cl (cl s) = cl s

/-! ## Part 2: Implication Presentations -/

/-- A closure presentation: a finite set of rules `(premises, conclusion)`. -/
abbrev ClosurePresentation (α : Type*) [DecidableEq α] := Finset (Finset α × α)

/-- A set `s` is closed under a presentation `P`. -/
def ClosedUnder {α : Type*} [DecidableEq α]
    (P : ClosurePresentation α) (s : Set α) : Prop :=
  ∀ rule ∈ P, (↑rule.1 : Set α) ⊆ s → rule.2 ∈ s

/-- The closure of `s` under presentation `P`: intersection of all closed supersets. -/
def GeneratedClosure {α : Type*} [DecidableEq α]
    (P : ClosurePresentation α) (s : Set α) : Set α :=
  ⋂₀ {t : Set α | s ⊆ t ∧ ClosedUnder P t}

/-- A closure operator has rank bounded by `r`. -/
def ClosureRankBounded {α : Type*} [DecidableEq α]
    (cl : Set α → Set α) (r : ℕ) : Prop :=
  ∃ P : ClosurePresentation α,
    (∀ rule ∈ P, rule.1.card ≤ r) ∧
    ∀ s, GeneratedClosure P s = cl s

/-! ## Part 3: Residual Equivalence and Generators -/

/-- Residual equivalence: `x` and `y` have the same closure profile. -/
def ResidualEquivalent {α : Type*} (cl : Set α → Set α) (x y : α) : Prop :=
  ∀ s : Set α, x ∈ cl s ↔ y ∈ cl s

/-- A residual generator pairs a target element with a support set. -/
@[ext]
structure ResidualGenerator (α : Type*) where
  target : α
  support : Finset α

instance {α : Type*} [DecidableEq α] : DecidableEq (ResidualGenerator α) :=
  fun a b =>
    if ht : a.target = b.target then
      if hs : a.support = b.support then
        isTrue (ResidualGenerator.ext ht hs)
      else isFalse (fun h => hs (h ▸ rfl))
    else isFalse (fun h => ht (h ▸ rfl))

/-- A minimal support for `x` under `cl`: `A` generates `x` and no proper subset does. -/
def IsMinimalSupport {α : Type*} [DecidableEq α]
    (cl : Set α → Set α) (x : α) (A : Finset α) : Prop :=
  x ∈ cl (↑A : Set α) ∧ ∀ B : Finset α, B ⊂ A → x ∉ cl (↑B : Set α)

/-- The set of all minimal supports for a given target `x`. -/
def minimalSupports {α : Type*} [DecidableEq α] [Fintype α]
    (cl : Set α → Set α) (x : α) : Finset (Finset α) :=
  @Finset.filter _ (fun A' => IsMinimalSupport cl x A')
    (fun _ => Classical.propDecidable _) Finset.univ

/-! ## Part 4: Canonical Residual Basis -/

/-- The canonical residual basis: the set of all minimal residual generators. -/
def canonicalBasis {α : Type*} [DecidableEq α] [Fintype α]
    (cl : Set α → Set α) : Finset (ResidualGenerator α) :=
  Finset.univ.biUnion fun x =>
    (minimalSupports cl x).image fun A => ⟨x, A⟩

/-- A set of residual generators forms a canonical basis:
    1. Every generator is minimal.
    2. Closure membership ↔ containing some generator's support. -/
def IsCanonicalBasis {α : Type*} [DecidableEq α] [Fintype α]
    (cl : Set α → Set α) (B : Finset (ResidualGenerator α)) : Prop :=
  (∀ g ∈ B, IsMinimalSupport cl g.target g.support) ∧
  (∀ x : α, ∀ s : Set α,
    x ∈ cl s ↔ ∃ g ∈ B, g.target = x ∧ (↑g.support : Set α) ⊆ s)

/-! ## Part 5: Monotone Circuits -/

/-- A monotone Boolean circuit over inputs from `α`. -/
inductive MonotoneCircuit (α : Type*)
  | input : α → MonotoneCircuit α
  | top : MonotoneCircuit α
  | bot : MonotoneCircuit α
  | conj : MonotoneCircuit α → MonotoneCircuit α → MonotoneCircuit α
  | disj : MonotoneCircuit α → MonotoneCircuit α → MonotoneCircuit α

namespace MonotoneCircuit

/-- Evaluate a monotone circuit on a set `s`. -/
def eval {α : Type*} : MonotoneCircuit α → Set α → Prop
  | input a, s => a ∈ s
  | top, _ => True
  | bot, _ => False
  | conj c₁ c₂, s => c₁.eval s ∧ c₂.eval s
  | disj c₁ c₂, s => c₁.eval s ∨ c₂.eval s



end MonotoneCircuit

/-- Build a conjunction circuit from a list of inputs. -/
def conjOfList {α : Type*} : List α → MonotoneCircuit α
  | [] => .top
  | a :: as => .conj (.input a) (conjOfList as)

/-- Build a disjunction of circuits from a list. -/
def disjOfList {α : Type*} : List (MonotoneCircuit α) → MonotoneCircuit α
  | [] => .bot
  | c :: cs => .disj c (disjOfList cs)



/-! ## Part 6: Closure Circuit and Reconstruction -/

/-- A closure circuit: one monotone circuit per output element. -/
structure ClosureCircuit (α : Type*) where
  output : α → MonotoneCircuit α

/-- A closure circuit correctly computes a closure operator. -/
def CircuitComputesClosure {α : Type*}
    (C : ClosureCircuit α) (cl : Set α → Set α) : Prop :=
  ∀ x s, (C.output x).eval s ↔ x ∈ cl s

/-- Reconstruct a closure circuit from a closure operator using its minimal
    supports: for each `x`, build `⋁_{A ∈ minSupp(x)} ⋀_{a ∈ A} input(a)`. -/
def reconstructClosureCircuit {α : Type*} [DecidableEq α] [Fintype α]
    (cl : Set α → Set α) : ClosureCircuit α where
  output x := disjOfList
    ((minimalSupports cl x).val.toList.map fun A => conjOfList A.val.toList)

/-! ## Part 7: GeneratedClosure is a Closure Operator -/

variable {α : Type*} [DecidableEq α] [Fintype α]






/-! ## Part 8: Minimal Support Theory -/

/-
Every element in a closure (applied to a finite set) admits a minimal support.
-/

/-
Closure membership ↔ existence of a minimal support within any generating set.
-/

/-! ## Part 9: Canonical Basis Theorems -/

/-
The canonical basis satisfies the basis property.
-/

/-
Any two canonical bases are equal.
-/


/-! ## Part 10: Circuit Correctness -/

/-
The reconstructed DNF circuit correctly computes the closure operator.
-/

/-! ## Part 11: Main Duality Theorem -/




end

end ClosureCircuitDuality


