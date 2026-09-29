-- Prove2me | Theorems.Thm_always_satisfies_box_gfp
-- name    : always_satisfies_box_gfp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T15:00:33.71092+00:00
-- url     : https://prove2.me/theorems/771491d0-8f67-4f1c-b384-af631e845d37
-- title:
--   Always satisfies box gfp
-- statement:
--   Formal statement of `always_satisfies_box_gfp` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem always_satisfies_box_gfp(T : FTS σ) (P : Set σ) :
--       ∀ s, satisfiesAlways T P s →
--         s ∈ sSup {X : Set σ | X ⊆ boxOp T P X} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/TemporalFixpointSemantics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/TemporalFixpointSemantics.lean#L258

-- Thm stub generated from Logic/PosetTheory/TemporalFixpointSemantics.lean
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

theorem always_satisfies_box_gfp(T : FTS σ) (P : Set σ) :
    ∀ s, satisfiesAlways T P s →
      s ∈ sSup {X : Set σ | X ⊆ boxOp T P X} := by sorry
