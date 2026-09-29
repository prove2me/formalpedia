-- Prove2me | Definitions.Def_Bridges_PosetTheory_KnuthBendixCompletion
-- name    : Bridges_PosetTheory_KnuthBendixCompletion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:01.202981+00:00
-- url     : https://prove2.me/theorems/067f527b-4b94-4db8-8053-b6517eb47809
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_KnuthBendixCompletion
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.KnuthBendixCompletion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/KnuthBendixCompletion.lean by skeleton subtraction
import Mathlib

/-!
# Certified Knuth-Bendix Completion: Automated Synthesis of Convergent Rewrite Systems

## Overview

This file formalizes the core theory of Knuth-Bendix completion at the level of
abstract rewrite systems (ARS). We establish:

1. **Newman's Lemma**: Terminating + locally confluent ⟹ confluent
2. **Equational theory preservation**: KB completion steps preserve the equational theory
3. **Convergent completion theorem**: Terminated completion yields a convergent system
4. **Bridge to certified optimization**: Convergent systems yield semantics-preserving normalizers

These results close the loop from equational specifications to certified optimizers:
  equations → KB completion → convergence certificate → normalizer → optimizer

## Design

We work at the level of abstract rewrite systems, parameterized by a type `T` and
a step relation `R : T → T → Prop`. This separates the logical structure of
completion from syntactic details of first-order terms, enabling the theorems
to apply to any concrete term algebra.

## Lineage

Builds on `Pythagorean/ConvergentRewriteOptimizer.lean` conceptually:
- Extends the `CertifiedNormalizer` / `RewriteSound` architecture
- The completion pipeline composes with the existing optimizer architecture
-/

open Relation

namespace KnuthBendix

/-! ## Part 1: Abstract Rewrite System Properties -/

/-- A relation is **terminating** (strongly normalizing) if the inverse is well-founded. -/
def IsTerminating {T : Type*} (R : T → T → Prop) : Prop :=
  WellFounded (fun a b => R b a)

/-- A term is in **normal form** w.r.t. `R` if no rule applies. -/
def IsNF {T : Type*} (R : T → T → Prop) (t : T) : Prop :=
  ∀ u, ¬R t u

/-- `R` is **locally confluent** if single-step divergences can be joined. -/
def IsLocallyConfluent {T : Type*} (R : T → T → Prop) : Prop :=
  ∀ ⦃t u₁ u₂ : T⦄, R t u₁ → R t u₂ →
    ∃ v, ReflTransGen R u₁ v ∧ ReflTransGen R u₂ v

/-- `R` is **confluent** if all divergences can be joined. -/
def IsConfluent {T : Type*} (R : T → T → Prop) : Prop :=
  ∀ ⦃t u₁ u₂ : T⦄, ReflTransGen R t u₁ → ReflTransGen R t u₂ →
    ∃ v, ReflTransGen R u₁ v ∧ ReflTransGen R u₂ v

/-- `R` is **convergent** if it is both terminating and confluent. -/
def IsConvergent {T : Type*} (R : T → T → Prop) : Prop :=
  IsTerminating R ∧ IsConfluent R


/-- A rewrite relation is **sound** for an evaluation function if every
    single-step rewrite preserves evaluation in every model. -/
def IsSound {T A α : Type*} (R : T → T → Prop) (eval : (α → A) → T → A) : Prop :=
  ∀ ⦃s t : T⦄, R s t → ∀ (ι : α → A), eval ι s = eval ι t

/-- A **certified normalizer** packages a rewrite relation with a normal-form
    function and correctness witnesses. -/
structure CertifiedNorm (T : Type*) where
  /-- The oriented rewrite relation. -/
  R : T → T → Prop
  /-- The normal-form function. -/
  nf : T → T
  /-- The normal form is always in normal form. -/
  nf_normal : ∀ t, IsNF R (nf t)
  /-- `t` rewrites to `nf t`. -/
  nf_reduces : ∀ t, ReflTransGen R t (nf t)
  /-- Normal forms are unique. -/
  nf_unique : ∀ t u, IsNF R u → ReflTransGen R t u → u = nf t

/-! ## Part 2: Newman's Lemma -/

/-
If `t` is in normal form and `t →* u`, then `t = u`.
-/

/-
**Newman's Lemma.** A terminating, locally confluent ARS is confluent.

This is the cornerstone of Knuth-Bendix completion. It reduces confluence
(a global property) to local confluence (checkable via critical pairs).

**Proof sketch.** Well-founded induction on `t` using termination.
Given `t →* u₁` and `t →* u₂`, if either path is trivial, done.
Otherwise `t → s₁ →* u₁` and `t → s₂ →* u₂`. Local confluence
gives a join of `s₁, s₂` at some `w`. Inductive hypothesis on `s₁`
(smaller than `t`) joins `w` and `u₁` at some `v₁`. Then inductive
hypothesis on `w` (reachable from `s₂`, smaller than `t`) joins `v₁`
with the path from `s₂` to `u₂`.
-/

/-
In a convergent system, normal forms are unique.
-/

/-
In a terminating system, every term has a normal form.
-/

/-
A convergent system has a unique normal form for each term.
-/

/-! ## Part 3: Multi-step Soundness -/

/-
Multi-step rewrite soundness: if single steps preserve evaluation,
    so does the reflexive-transitive closure.
-/

/-
The master optimizer theorem: a convergent sound rewrite system's normalizer
    preserves evaluation.
-/

/-! ## Part 4: Equational Theory -/

/-- The **equational theory** of `R` is the equivalence closure of `R`. -/
def EqTheory {T : Type*} (R : T → T → Prop) : T → T → Prop := EqvGen R


/-
The reflexive-transitive closure is contained in the equational theory.
-/

/-
In a convergent system, two terms have the same normal form iff they are
in the same equational theory class.
-/

/-! ## Part 5: Completion State and Steps -/

/-- A **completion state** for Knuth-Bendix completion. -/
structure CompletionState (T : Type*) where
  /-- Oriented rewrite rules. -/
  rules : T → T → Prop
  /-- Pending equations. -/
  pending : T → T → Prop

/-- The combined theory of a completion state. -/
def CompletionState.theory {T : Type*} (S : CompletionState T) : T → T → Prop :=
  fun a b => S.rules a b ∨ S.pending a b

/-- A completion state is **finished** if no equations are pending. -/
def CompletionState.isFinished {T : Type*} (S : CompletionState T) : Prop :=
  ∀ a b, ¬S.pending a b

/-- A **KB completion step** preserves the equational theory. -/
structure KBStep {T : Type*} (S S' : CompletionState T) : Prop where
  theory_preserved : ∀ a b, EqTheory S'.theory a b ↔ EqTheory S.theory a b

/-- A **completion sequence** is a chain of KB steps. -/
def CompletionSequence {T : Type*} (S S' : CompletionState T) : Prop :=
  ReflTransGen (fun X Y => KBStep X Y) S S'

/-! ## Part 6: Completion Correctness -/

/-
**A sequence of KB steps preserves the equational theory.**
-/

/-
When completion finishes, the rules' equational theory equals
    the finished state's theory (since pending is empty).
-/

/-
**The Capstone Theorem: Terminated KB completion yields a convergent system.**

If completion runs from `S₀` to `S_final` where:
- Each step preserves the equational theory
- The final state has no pending equations
- The final rules are terminating
- The final rules are locally confluent (all critical pairs joined)

Then the final system is convergent and has the same equational theory.
-/

/-! ## Part 7: Bridge to Certified Optimizer -/


/-
**KB completion composes with certified optimization.**

The full pipeline: equations → completion → convergent system → normalizer → optimizer.
-/

/-
The normalizer is idempotent.
-/

/-
Two terms with the same normal form evaluate identically.
-/

/-! ## Part 8: Concrete Example — Boolean Ring Rewriting -/

/-- A simple term type for Boolean ring expressions. -/
inductive BoolTerm
  | var : Nat → BoolTerm
  | zero : BoolTerm
  | one : BoolTerm
  | add : BoolTerm → BoolTerm → BoolTerm
  | mul : BoolTerm → BoolTerm → BoolTerm
  deriving DecidableEq, Repr

/-- Evaluation of Boolean ring terms in `ZMod 2`. -/
def BoolTerm.eval (ι : Nat → ZMod 2) : BoolTerm → ZMod 2
  | .var n => ι n
  | .zero => 0
  | .one => 1
  | .add e₁ e₂ => e₁.eval ι + e₂.eval ι
  | .mul e₁ e₂ => e₁.eval ι * e₂.eval ι

/-- The idempotency rewrite: `x * x → x` (valid in Boolean rings). -/
inductive BoolIdemRewrite : BoolTerm → BoolTerm → Prop
  | idem (e : BoolTerm) : BoolIdemRewrite (.mul e e) e

/-
The idempotency rewrite is sound in `ZMod 2`.
-/

/-- The involution rewrite: `x + x → 0` (valid in characteristic 2). -/
inductive BoolInvolRewrite : BoolTerm → BoolTerm → Prop
  | invol (e : BoolTerm) : BoolInvolRewrite (.add e e) .zero

/-
The involution rewrite is sound in `ZMod 2`.
-/

end KnuthBendix


