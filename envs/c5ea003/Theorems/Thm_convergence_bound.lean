-- Prove2me | Theorems.Thm_convergence_bound
-- name    : convergence_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T15:01:59.685345+00:00
-- url     : https://prove2.me/theorems/0d5a7157-1e44-4dfd-893b-9d1652a8db24
-- title:
--   Convergence bound
-- statement:
--   Formal statement of `convergence_bound` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem convergence_bound    (F : α → α) (hF : Monotone F) :
--       ∃ n : ℕ, n ≤ Fintype.card α ∧ descIter F n = descIter F (n + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/TemporalFixpointSemantics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/TemporalFixpointSemantics.lean#L147

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

theorem convergence_bound    (F : α → α) (hF : Monotone F) :
    ∃ n : ℕ, n ≤ Fintype.card α ∧ descIter F n = descIter F (n + 1) := by sorry
