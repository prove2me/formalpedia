-- Prove2me | solution 1 for always_satisfies_box_gfp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:50:31.002736+00:00
-- url     : https://prove2.me/submissions/0726fe85-dbc8-4610-a47d-f7f6cbca4bd3

-- Sol generated from Logic/PosetTheory/TemporalFixpointSemantics.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalFixpointSemantics
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Temporal Stone Duality: Fixpoint Semantics and Algebraic Model Checking

This file establishes the core theorems connecting temporal logic semantics
to greatest-fixpoint computation in finite lattices, and proves that
behavioral equivalence is exactly captured by agreement on temporally
definable predicates.

## Main results

### Fixpoint Theory on Finite Complete Lattices
* `descending_chain_stabilizes` — F^n(⊤) stabilizes for monotone F on finite lattice
* `stabilized_iterate_is_fixpoint` — the stabilized iterate is a fixpoint of F
* `stabilized_iterate_is_greatest_fixpoint` — it is the *greatest* fixpoint
* `finite_gfp_exists` — existence of the greatest fixpoint
* `finite_gfp_eq_iterate` — gfp F = F^n(⊤) for some computable n

### Temporal Logic and Model Checking
* `boxOp_mono` — the box/safety operator is monotone
* `box_gfp_satisfies_always` — states in gfp satisfy "always P"
* `always_satisfies_box_gfp` — states satisfying "always P" are in gfp
* `box_semantics_iff_gfp` — "always P" ≡ gfp of the safety operator

### Behavioral Equivalence and Separation
* `behavioral_equiv_iff_eq` — behavioral equivalence ↔ equality of states
* `temporal_dual_separation` — equal dual points ↔ equal states
* `temporal_stone_duality_exact_theory` — flagship recovery theorem

### Order Duality
* `gfp_compl_eq_lfp_dual` — ν/μ duality via complementation
-/


open Set Function Finset Classical

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Part I: Fixpoint Theory on Finite Complete Lattices

We prove that for any monotone endomorphism on a finite complete lattice,
descending Kleene iteration from ⊤ converges to the greatest fixpoint.
This is the computational heart of temporal model checking. -/


variable {α : Type*} [Fintype α] [CompleteLattice α]












/-
**Convergence bound**: The iteration stabilizes within Fintype.card α steps.
-/


/-! ## Part II: Finite Transition Systems and Temporal Logic

We define a temporal logic over finite transition systems and prove
that the "always" operator corresponds to greatest-fixpoint computation. -/



variable {σ : Type*} [Fintype σ] [DecidableEq σ]











/-! ### Box Semantics = Greatest Fixpoint -/


/-
States in the gfp of boxOp satisfy "always P".
-/

/-
States satisfying "always P" are in the gfp.
-/





/-! ## Part III: Behavioral Equivalence and Separation -/


variable {σ : Type*} [Fintype σ] [DecidableEq σ]














/-! ## Part IV: The Duality Theory -/


variable {σ : Type*} [Fintype σ] [DecidableEq σ]



/-
**Flagship: Temporal Stone Duality recovers exact theory.**
    There exists a canonical family of temporally definable predicates that
    separates all states — two states agree on all predicates iff they are equal.
-/



/-! ## Part V: Idempotent Semiring Structure -/


variable {σ : Type*}







variable {σ : Type*} [Fintype σ] [DecidableEq σ]





/-! ## Part VI: Order Duality (ν ↔ μ via Complement) -/


variable {σ : Type*}





variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-
**Temporal duality**: The complement of the gfp of F equals
    the lfp of the dual operator.
-/


/-! ## Part VII: Decidability -/


variable {σ : Type*} [Fintype σ] [DecidableEq σ]





-- open removed: section is not a namespace
theorem solution(T : FTS σ) (P : Set σ) :
    ∀ s, satisfiesAlways T P s →
      s ∈ sSup {X : Set σ | X ⊆ boxOp T P X} := by
  intro s hs;
  -- Let $W = \{s \mid \text{satisfiesAlways } T P s\}$.
  set W := {s : σ | satisfiesAlways T P s};
  -- We need to show that $W \subseteq \text{boxOp } T P W$.
  have hW_subset_boxOp : W ⊆ boxOp T P W := by
    intro s hs;
    constructor;
    · exact hs 0 s ( by tauto );
    · intro t ht;
      intro n u hu;
      exact hs ( n + 1 ) u ( by exact ⟨ t, ht, hu ⟩ );
  exact Set.mem_sUnion.2 ⟨ W, hW_subset_boxOp, hs ⟩
