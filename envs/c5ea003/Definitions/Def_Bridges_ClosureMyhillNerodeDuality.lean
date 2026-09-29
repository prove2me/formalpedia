-- Prove2me | Definitions.Def_Bridges_ClosureMyhillNerodeDuality
-- name    : Bridges_ClosureMyhillNerodeDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:25.285316+00:00
-- url     : https://prove2.me/theorems/b02ee4a3-472a-43b5-a330-11bce440791b
-- title:
--   Aether Catalog definitions — Bridges_ClosureMyhillNerodeDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureMyhillNerodeDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureMyhillNerodeDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closure–Myhill–Nerode Duality via Idempotent Residual Semimodules

This file establishes a Myhill–Nerode theorem for closure-driven computation.
The main result shows that finite closure semantics with residual generation
and idempotent join structure yield a canonical minimal deterministic recognizer,
unique up to isomorphism among all deterministic closure-compatible recognizers.

## Main definitions

* `ClosureSystem` — a closure-compatible transition system
* `residualProfile` — the closure-stable continuation semantics of a word
* `NerodeEq` — Nerode equivalence (same acceptance behavior for all suffixes)
* `ClosureAutomaton` — abstract deterministic automaton
* `canonicalClosureAutomaton` — the canonical automaton on Nerode classes

## Main results

* `nerodeEq_right_congruence` — Nerode equivalence is a right congruence
* `nerodeEq_iff_residualProfile` — Nerode equivalence equals residual profile equality
* `reachableResiduals_closed` — reachable residuals are closed sets
* `closure_myhill_nerode` — finiteness of residuals gives a canonical recognizer
* `recognizer_refines_residuals` — any recognizer refines residual classes
* `closureJoin_assoc` — reachable residuals form a join-semilattice

## References

This is a closure-semantic analogue of the classical Myhill–Nerode theorem,
where minimal states are extracted from the algebra of residual closures
rather than postulated externally. The key insight is that closure operators
induce a canonical residual algebra whose join-irreducible elements determine
the state space of the minimal recognizer.
-/


open Set Function

universe u v

/-! ## Core Definitions -/

/-- A closure-compatible transition system over configurations `X` and alphabet `α`.

This packages a closure operator on `Set X`, a deterministic step function,
and an acceptance predicate, together with the axioms making the system
well-behaved: extensivity, monotonicity, idempotence, and closure compatibility
of the transition. -/
structure ClosureSystem (X : Type u) (α : Type v) where
  /-- The closure operator on sets of configurations. -/
  cl : Set X → Set X
  /-- Deterministic transition function. -/
  step : X → α → X
  /-- The set of accepting configurations. -/
  accept : Set X
  /-- Extensivity: every set is contained in its closure. -/
  cl_extensive : ∀ A, A ⊆ cl A
  /-- Monotonicity: closure preserves inclusion. -/
  cl_mono : ∀ {A B : Set X}, A ⊆ B → cl A ⊆ cl B
  /-- Idempotence: closing a closed set does nothing. -/
  cl_idem : ∀ A, cl (cl A) = cl A
  /-- Closure compatibility: the direct image of a closed set under a letter action
      is contained in the closure of the direct image. -/
  step_closure_compatible :
    ∀ (a : α) (A : Set X),
      (fun x => step x a) '' (cl A) ⊆ cl ((fun x => step x a) '' A)

variable {X : Type u} {α : Type v}

namespace ClosureSystem

/-! ## Word action and residual profiles -/

/-- Execute a word (list of letters) from a configuration. -/
def stepWord (S : ClosureSystem X α) : X → List α → X
  | x, [] => x
  | x, a :: w => S.stepWord (S.step x a) w

/-- The residual profile of a word `w`: the closure of the set of configurations
    from which executing `w` leads to an accepting configuration. This is the
    closure-stable continuation semantics induced by `w`. -/
def residualProfile (S : ClosureSystem X α) (w : List α) : Set X :=
  S.cl {x | S.stepWord x w ∈ S.accept}

/-! ## Lemma: stepWord distributes over append -/


/-! ## Nerode equivalence (closure-semantic version) -/

/-- Two words are Nerode-equivalent (in the closure-semantic sense) if they have
    the same residual profile for all suffixes. That is, the closure-stable
    continuation semantics agrees for every continuation word. -/
def NerodeEq (S : ClosureSystem X α) (u v : List α) : Prop :=
  ∀ z : List α, S.residualProfile (u ++ z) = S.residualProfile (v ++ z)

/-- The simpler notion: two words have the same residual profile. -/
def ResidualEq (S : ClosureSystem X α) (u v : List α) : Prop :=
  S.residualProfile u = S.residualProfile v

/-! ## Theorem A: Nerode equivalence is a right congruence -/

/-
Nerode equivalence is a right congruence: if `u ~ v`, then `u ++ [a] ~ v ++ [a]`
    for any letter `a`.
-/

/-
Nerode equivalence is a right congruence for arbitrary suffixes.
-/

/-
Nerode equivalence implies residual equality (take z = []).
-/

/-! ## Nerode equivalence is an equivalence relation -/





/-! ## Theorem B: Acceptance factors through Nerode classes -/

/-
If two words are Nerode-equivalent, then for any configuration `x`,
    `x` is in one residual profile iff it is in the other.
-/

/-! ## The set of reachable residuals -/

/-- The set of all reachable residual profiles. -/
def ReachableResiduals (S : ClosureSystem X α) : Set (Set X) :=
  {R | ∃ w : List α, S.residualProfile w = R}

/-! ## Join-semilattice structure on closed sets -/

/-- A set is closed if it is a fixed point of the closure operator. -/
def IsClosed (S : ClosureSystem X α) (A : Set X) : Prop :=
  S.cl A = A





/-- The join operation on closed sets: close the union. -/
def closureJoin (S : ClosureSystem X α) (P Q : Set X) : Set X :=
  S.cl (P ∪ Q)







/-
The join operation is associative.
-/

/-! ## Closure Automaton -/

/-- A deterministic automaton with potentially infinite state type. -/
structure ClosureAutomaton (α : Type v) where
  /-- State type. -/
  State : Type*
  /-- Initial state. -/
  init : State
  /-- Transition function. -/
  transition : State → α → State
  /-- Acceptance predicate. -/
  accepting : State → Prop

namespace ClosureAutomaton

/-- Execute a word in a closure automaton from a given state. -/
def run (A : ClosureAutomaton α) : A.State → List α → A.State
  | s, [] => s
  | s, a :: w => A.run (A.transition s a) w

/-- A word is accepted by the automaton. -/
def acceptsWord (A : ClosureAutomaton α) (w : List α) : Prop :=
  A.accepting (A.run A.init w)


end ClosureAutomaton

/-! ## Morphism between automata -/


/-! ## Canonical closure automaton construction -/


/-! ## Equivalence relation on automaton states -/

/-- Two automaton states are behaviorally equivalent if they accept the same
    continuations. -/
def BehavioralEq (A : ClosureAutomaton α) (s t : A.State) : Prop :=
  ∀ w : List α, A.accepting (A.run s w) ↔ A.accepting (A.run t w)






/-! ## Recognizer definition -/

/-- A recognizer of a closure system: an automaton whose acceptance behavior
    matches closure-membership semantics. The automaton accepts `w` iff `x₀`
    is in the residual profile of `w`. This is the closure-semantic notion
    of recognition, where membership in the *closure* of the accepting
    preimage determines acceptance. -/
def IsRecognizer (S : ClosureSystem X α) (x₀ : X) (A : ClosureAutomaton α) : Prop :=
  ∀ w : List α, A.acceptsWord w ↔ x₀ ∈ S.residualProfile w

/-! ## Residual equivalence as an equivalence relation -/





/-! ## Finiteness theorem -/

/-
When the set of reachable residuals is finite, every reachable residual is closed,
    giving a finite-state canonical automaton. This is the closure-semantic
    Myhill–Nerode theorem: finite residual profiles determine a finite canonical
    recognizer.
-/

/-! ## Minimality: states of any recognizer refine residual classes -/

/-
If an automaton recognizes a closure system, then states reached by
    Nerode-equivalent words are behaviorally equivalent.
    This shows the canonical residual automaton is minimal: its states
    are the coarsest partition compatible with recognition.
-/

/-
Any two recognizers of the same closure system have the same behavioral
    equivalence classes: Nerode equivalence uniquely determines the state
    structure (up to behavioral equivalence). This is the uniqueness part
    of the closure Myhill–Nerode theorem.
-/

end ClosureSystem


