-- Prove2me | solution 1 for ClosureCircuitDuality.canonical_basis_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:06:48.576147+00:00
-- url     : https://prove2.me/submissions/430993b3-29d2-43ed-9192-2867d18a475a

-- Sol generated from Bridges/ClosureCircuitDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureCircuitDuality
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


open ClosureCircuitDuality

open Set Finset

noncomputable section

/-! ## Part 1: Core Definitions -/


/-! ## Part 2: Implication Presentations -/





/-! ## Part 3: Residual Equivalence and Generators -/






/-! ## Part 4: Canonical Residual Basis -/



/-! ## Part 5: Monotone Circuits -/


open MonotoneCircuit









/-! ## Part 6: Closure Circuit and Reconstruction -/




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






open ClosureCircuitDuality in
theorem solution    (cl : Set α → Set α) (_hcl : IsClosureOperator cl)
    (B₁ B₂ : Finset (ResidualGenerator α))
    (h₁ : IsCanonicalBasis cl B₁) (h₂ : IsCanonicalBasis cl B₂) :
    B₁ = B₂ := by
  apply Finset.ext
  intro g
  constructor
  intro hg₁
  obtain ⟨g', hg₂, hg₃⟩ := h₂.2 g.target (↑g.support : Set α) |>.1 (h₁.1 g hg₁ |>.1)
  have hg₄ : g'.target = g.target ∧ (↑g'.support : Set α) ⊆ ↑g.support := by
    exact hg₃
  have hg₅ : g'.support = g.support := by
    have hg₅ : IsMinimalSupport cl g.target g.support := by
      exact h₁.1 g hg₁
    have hg₆ : IsMinimalSupport cl g.target g'.support := by
      have := h₂.1 g' hg₂; aesop;
    simp_all +decide [ IsMinimalSupport ];
    grind
  have hg₆ : g' = g := by
    cases g ; cases g' ; aesop
  aesop;
  intro hg;
  obtain ⟨g', hg'⟩ := h₁.2 g.target (↑g.support : Set α) |>.1 (h₂.1 g hg |>.1);
  have hg'_eq_g : g'.support = g.support := by
    have hg'_eq_g : ∀ B : Finset α, B ⊂ g.support → g.target ∉ cl (↑B : Set α) := by
      exact h₂.1 g hg |>.2;
    exact Classical.not_not.1 fun h => hg'_eq_g g'.support ( lt_of_le_of_ne ( by aesop ) h ) ( by simpa [ hg'.2.1 ] using h₁.1 g' hg'.1 |>.1 );
  cases g ; cases g' ; aesop
