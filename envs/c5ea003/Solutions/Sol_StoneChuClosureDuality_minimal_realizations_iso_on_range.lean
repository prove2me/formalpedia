-- Prove2me | solution 1 for StoneChuClosureDuality.minimal_realizations_iso_on_range
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:48:53.383024+00:00
-- url     : https://prove2.me/submissions/d2d1d6f2-8a61-47fb-9528-0af15792a20a

-- Sol generated from Bridges/StoneChuClosureDuality.lean
import Mathlib
import Definitions.Def_Bridges_StoneChuClosureDuality
/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


/-!
# Stone–Chu Closure Duality for Finite Closure Systems with Observables

This file formalizes a bridge theorem connecting **finite closure systems with
separating observables** to **minimal finite Kripke-style realizations**, establishing
a certified equivalence between closure dynamics and logical realization theory.

## Mathematical Overview

Given a finite type `α` with a closure operator `cl : Set α → Set α` and a finite
family of closure-compatible observables `obs : ι → Set α → Set α`, we define:

- **Observational equivalence** `ObsEquiv cl obs x y`: two elements are equivalent
  when every observable context maps them to the same closed membership.
- **Closed theories**: the set of observable-context / closed-set pairs true at a point.
- **Canonical Kripke realization**: states are equivalence classes under observational
  equivalence, with transitions induced by observables.

## Main Results

* `obsEquiv_equivalence` — Observational equivalence is an equivalence relation.
* `obsEquiv_iff_closedTheory` — Observational equivalence iff equal closed theories.
* `canonicalKripke_obsEquivalent` — The canonical realization is observationally equivalent.
* `canonical_factorization` — Any realization factors through the canonical one.
* `canonicalKripke_minimal` — The canonical realization is minimal.
* `chu_collapse_eq_obsEquiv` — Chu biextensional collapse = observational equivalence.
* `stone_chu_closure_duality` — The flagship duality theorem.
* `reconstruct_minimal_kripke_correct` — Certified reconstruction correctness.
* `exists_minimal_with_iso` — Existence + range-uniqueness of minimal realization.

## Cross-Domain Connections

- **Automata theory / Myhill–Nerode**: `ObsEquiv` is a modal analog of Nerode equivalence;
  the minimal realization is the certified minimal automaton.
- **Coalgebraic modal logic**: The factorization theorem is a minimality statement for
  finite coalgebraic semantics.
- **Formal concept analysis / Chu spaces**: States vs observables form a Chu correspondence;
  closed theories are concept intents, prime classes are extents.
- **Abstract interpretation**: The closure operator is an abstract domain completion;
  the minimal realization is the smallest sound logical machine.
-/

set_option maxHeartbeats 1600000

open Set Function

noncomputable section

open StoneChuClosureDuality

/-! ## §1. Closure Operator Axiomatics -/





/-! ## §2. Observable Contexts -/




/-! ## §3. Observational Equivalence -/







/-! ## §4. Closed Theories -/



/-! ## §5. Congruence Properties -/



/-! ## §6. Finite Quotient -/





/-! ## §7. Kripke Realization -/


attribute [instance] KripkeRealization.state_finite




/-! ## §8. Morphisms and Factorization -/





/-! ## §9. Uniqueness (isomorphism on range) -/


/-! ## §10. Chu Space Structure -/







/-! ## §11. Closed Theory Lattice -/




/-! ## §12. Valuation Characterization -/


/-! ## §13. Flagship Duality Theorem -/


/-! ## §14. Algorithmic Reconstruction -/



/-! ## §15. Existence and Range-Uniqueness -/



open StoneChuClosureDuality in
theorem solution{α : Type*} {ι : Type*}
    [Fintype α] [Inhabited α]
    {cl : Set α → Set α} {obs : ι → Set α → Set α}
    {S₁ S₂ : Type*}
    (K₁ : KripkeRealization cl obs S₁) (K₂ : KripkeRealization cl obs S₂)
    (h₁ : IsObsEquivalent K₁) (h₂ : IsObsEquivalent K₂) :
    ∃ (fwd : S₁ → S₂) (bwd : S₂ → S₁),
      (∀ x : α, fwd (K₁.realize x) = K₂.realize x) ∧
      (∀ x : α, bwd (K₂.realize x) = K₁.realize x) ∧
      (∀ x : α, bwd (fwd (K₁.realize x)) = K₁.realize x) ∧
      (∀ x : α, fwd (bwd (K₂.realize x)) = K₂.realize x) := by
  classical
  let fwd : S₁ → S₂ := fun s =>
    if h : ∃ x : α, K₁.realize x = s then K₂.realize h.choose
    else K₂.realize default
  let bwd : S₂ → S₁ := fun s =>
    if h : ∃ x : α, K₂.realize x = s then K₁.realize h.choose
    else K₁.realize default
  have fwd_comm : ∀ x : α, fwd (K₁.realize x) = K₂.realize x := by
    intro x; simp only [fwd]
    split
    · next h => exact (h₂ _ _).mp ((h₁ _ _).mpr h.choose_spec)
    · next h => exact absurd ⟨x, rfl⟩ h
  have bwd_comm : ∀ x : α, bwd (K₂.realize x) = K₁.realize x := by
    intro x; simp only [bwd]
    split
    · next h => exact (h₁ _ _).mp ((h₂ _ _).mpr h.choose_spec)
    · next h => exact absurd ⟨x, rfl⟩ h
  exact ⟨fwd, bwd, fwd_comm, bwd_comm,
    fun x => by rw [fwd_comm, bwd_comm],
    fun x => by rw [bwd_comm, fwd_comm]⟩
