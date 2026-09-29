-- Prove2me | solution 1 for convergence_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:50:32.912663+00:00
-- url     : https://prove2.me/submissions/5ae242d8-5101-4ddd-9a80-92df33e1f4b3

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



/-- Descending iteration is antitone as a function of n. -/
theorem descIter_antitone' (F : α → α) (hF : Monotone F) :
    Antitone (descIter F) :=
  antitone_nat_of_succ_le (descIter_antitone F hF)









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
theorem solution    (F : α → α) (hF : Monotone F) :
    ∃ n : ℕ, n ≤ Fintype.card α ∧ descIter F n = descIter F (n + 1) := by
  by_contra! h;
  -- By the pigeonhole principle, among the Fintype.card α + 1 values descIter F 0, ..., descIter F (Fintype.card α), two must be equal.
  have h_pigeonhole : ∃ i j : ℕ, i < j ∧ i ≤ Fintype.card α ∧ j ≤ Fintype.card α ∧ descIter F i = descIter F j := by
    have h_pigeonhole : Finset.card (Finset.image (fun n => descIter F n) (Finset.range (Fintype.card α + 1))) ≤ Fintype.card α := by
      exact Finset.card_le_univ _;
    by_cases h_eq : ∀ i j : ℕ, i < j → i ≤ Fintype.card α → j ≤ Fintype.card α → descIter F i ≠ descIter F j;
    · exact absurd h_pigeonhole ( by rw [ Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm ( not_lt.mp fun hi' => h_eq _ _ hi' ( Finset.mem_range_succ_iff.mp hj ) ( Finset.mem_range_succ_iff.mp hi ) hij.symm ) ( not_lt.mp fun hj' => h_eq _ _ hj' ( Finset.mem_range_succ_iff.mp hi ) ( Finset.mem_range_succ_iff.mp hj ) hij ) ] ; simp +decide );
    · exact by push_neg at h_eq; exact h_eq;
  -- Since the chain is antitone, if descIter F i = descIter F j with i < j, then the chain must be constant from i to j.
  obtain ⟨i, j, hij, hi, hj, h_eq⟩ := h_pigeonhole
  have h_const : ∀ k, i ≤ k → k ≤ j → descIter F k = descIter F i := by
    intros k hk₁ hk₂
    have h_antitone : ∀ m n, m ≤ n → n ≤ Fintype.card α → descIter F m ≥ descIter F n := by
      exact fun m n mn hn => descIter_antitone' F hF mn;
    exact le_antisymm ( h_antitone _ _ hk₁ ( by linarith ) ) ( h_eq ▸ h_antitone _ _ hk₂ ( by linarith ) );
  exact h i hi ( h_const ( i + 1 ) ( by linarith ) ( by linarith ) ▸ rfl )
