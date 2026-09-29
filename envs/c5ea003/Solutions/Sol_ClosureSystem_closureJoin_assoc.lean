-- Prove2me | solution 1 for ClosureSystem.closureJoin_assoc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:10:49.594606+00:00
-- url     : https://prove2.me/submissions/e44693bc-586e-497d-94eb-40771f05b253

-- Sol generated from Bridges/ClosureMyhillNerodeDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureMyhillNerodeDuality
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


variable {X : Type u} {α : Type v}

open ClosureSystem

/-! ## Word action and residual profiles -/



/-! ## Lemma: stepWord distributes over append -/


/-! ## Nerode equivalence (closure-semantic version) -/



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


/-! ## Join-semilattice structure on closed sets -/













/-
The join operation is associative.
-/

/-! ## Closure Automaton -/


open ClosureAutomaton





/-! ## Morphism between automata -/


/-! ## Canonical closure automaton construction -/


/-! ## Equivalence relation on automaton states -/







/-! ## Recognizer definition -/


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


open ClosureSystem in
theorem solution(S : ClosureSystem X α) (P Q R : Set X) :
    S.closureJoin (S.closureJoin P Q) R =
      S.closureJoin P (S.closureJoin Q R) := by
  have h_union : (S.cl ((S.cl (P ∪ Q)) ∪ R)) = (S.cl (P ∪ Q ∪ R)) ∧ (S.cl (P ∪ (S.cl (Q ∪ R)))) = (S.cl (P ∪ Q ∪ R)) := by
    constructor;
    · apply Set.Subset.antisymm;
      · have h_union : S.cl (P ∪ Q) ∪ R ⊆ S.cl (P ∪ Q ∪ R) := by
          apply Set.union_subset;
          · exact S.cl_mono ( Set.subset_union_left );
          · exact fun x hx => S.cl_extensive _ ( Set.mem_union_right _ hx );
        exact S.cl_mono h_union |> Set.Subset.trans <| by simp +decide [ S.cl_idem ] ;
      · apply S.cl_mono;
        exact Set.union_subset_union ( S.cl_extensive _ ) Set.Subset.rfl;
    · refine' le_antisymm _ _;
      · have := S.cl_mono ( show P ∪ S.cl ( Q ∪ R ) ⊆ S.cl ( P ∪ Q ∪ R ) from ?_ );
        · exact this.trans ( by rw [ S.cl_idem ] );
        · simp +decide [ Set.union_assoc ];
          exact ⟨ fun x hx => S.cl_extensive _ ( Set.mem_union_left _ hx ), S.cl_mono ( Set.subset_union_right ) ⟩;
      · refine' S.cl_mono _;
        rintro x ( ( hx | hx ) | hx ) <;> [ exact Or.inl hx; exact Or.inr ( S.cl_extensive _ ( Set.mem_union_left _ hx ) ) ; exact Or.inr ( S.cl_extensive _ ( Set.mem_union_right _ hx ) ) ];
  exact h_union.1.trans h_union.2.symm
