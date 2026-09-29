-- Prove2me | solution 1 for FinRevSystem.forwardClosure_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:05:43.877649+00:00
-- url     : https://prove2.me/submissions/84122933-e5f1-4e03-bb43-c2dec3cc1632

-- Sol generated from Bridges/TemporalStoneBirkhoffDuality.lean
import Mathlib
import Definitions.Def_Bridges_CausalClosure
import Definitions.Def_Bridges_TemporalStoneBirkhoffDuality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Temporal Stone–Birkhoff Duality via Reversible Oracle Semirings

This file establishes a finite duality between reversible oracle transition systems
and temporal consistency algebras. The core insight is that reversible computation —
where every transition has an inverse — admits a canonical **causal completion**
obtained via idempotent closure operators, and this completion classifies systems
up to behavioral equivalence.

## Main results

* `causalCl_idempotent` — combined causal closure is idempotent
* `causalCompletion_canonical` — causal completion produces fixed points
* `behavioral_equiv_iff_fixed_iso` — behavioral equivalence ↔ completion isomorphism
* `causal_completion_minimal` — minimality of the causal completion
* `finite_temporal_stone_birkhoff_duality` — the flagship finite duality theorem
* `causalCompletion_universal_system` — universal property of the causal completion
-/

open Finset Function

/-! ## Finite Reversible Transition Systems -/


open FinRevSystem

variable {S : Type*} [Fintype S] [DecidableEq S] (X : FinRevSystem S)



/-! ## Forward Closure on Finset S -/


/-- Forward step is extensive. -/
theorem fwdStep_extensive (A : Finset S) : A ⊆ X.fwdStep A :=
  Finset.subset_union_left








/-
Forward closure is idempotent.
-/

/-! ## Causal Closure for Reversible Systems -/





/-! ## Causal Equivalence -/






/-! ## Causal Fixed Points -/


instance : PartialOrder X.CausalFixed := Subtype.partialOrder _


/-! ## Temporal Consistency Algebra -/


/-! ## Behavioral Equivalence -/






/-! ## Atoms -/



/-! ## Main Duality Theorem -/


/-! ## Universal Property of Causal Completion -/


/-! ## Certified Minimization -/


/-! ## Spec Functor (Object Level) -/


/-! ## Alg Functor (Object Level) -/


open FinRevSystem in
theorem solution(A : Finset S) :
    X.forwardClosure (X.forwardClosure A) = X.forwardClosure A := by
  -- To prove idempotence, it suffices to show that applying `fwdStep` Fintype.card S times stabilizes.
  have h_finite : ∀ n ≥ Fintype.card S, ∀ A : Finset S, X.fwdIter n A = X.fwdIter (Fintype.card S) A := by
    intro n hn A
    by_contra h_contra;
    -- Since the sequence is increasing and bounded above, it must stabilize.
    have h_stabilize : ∃ k ≤ Fintype.card S, X.fwdIter (k + 1) A = X.fwdIter k A := by
      by_cases h_stabilize : ∀ k ≤ Fintype.card S, X.fwdIter (k + 1) A ≠ X.fwdIter k A;
      · have h_card : ∀ k ≤ Fintype.card S, (X.fwdIter (k + 1) A).card > (X.fwdIter k A).card := by
          intro k hk
          have h_card : X.fwdIter (k + 1) A ⊇ X.fwdIter k A := by
            exact fwdStep_extensive X _;
          exact Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ h_card, Ne.symm ( h_stabilize k hk ) ⟩ );
        have h_card : (X.fwdIter (Fintype.card S + 1) A).card ≥ (X.fwdIter 0 A).card + (Fintype.card S + 1) := by
          have h_card : ∀ k ≤ Fintype.card S, (X.fwdIter (k + 1) A).card ≥ (X.fwdIter 0 A).card + (k + 1) := by
            intro k hk
            induction' k with k ih;
            · exact h_card 0 bot_le;
            · linarith [ ih ( Nat.le_of_succ_le hk ), h_card ( k + 1 ) hk ];
          exact h_card _ le_rfl;
        exact absurd h_card ( by linarith [ show Finset.card ( X.fwdIter ( Fintype.card S + 1 ) A ) ≤ Fintype.card S from Finset.card_le_univ _, show Finset.card ( X.fwdIter 0 A ) ≥ 0 from Nat.zero_le _ ] );
      · exact by push_neg at h_stabilize; exact h_stabilize;
    obtain ⟨ k, hk₁, hk₂ ⟩ := h_stabilize;
    -- Since $k \leq Fintype.card S$, we have $X.fwdIter n A = X.fwdIter k A$ for all $n \geq k$.
    have h_eq : ∀ n ≥ k, X.fwdIter n A = X.fwdIter k A := by
      intro n hn; induction hn <;> simp_all +decide [ FinRevSystem.fwdIter ] ;
    exact h_contra ( h_eq n ( by linarith ) ▸ h_eq ( Fintype.card S ) ( by linarith ) ▸ rfl );
  -- By definition of `forwardClosure`, we know that `forwardClosure A = fwdIter (Fintype.card S) A`.
  have h_forwardClosure : X.forwardClosure A = X.fwdIter (Fintype.card S) A := by
    rfl;
  convert h_finite ( Fintype.card S + Fintype.card S ) ( Nat.le_add_left _ _ ) A using 1;
  rw [ h_forwardClosure, show X.fwdIter ( Fintype.card S + Fintype.card S ) A = X.fwdIter ( Fintype.card S ) ( X.fwdIter ( Fintype.card S ) A ) from ?_ ];
  · rfl;
  · have h_finite : ∀ m n A, X.fwdIter (m + n) A = X.fwdIter m (X.fwdIter n A) := by
      intro m n A; induction' m with m ih generalizing A <;> simp_all +decide [ Nat.succ_add, FinRevSystem.fwdIter ] ;
    exact h_finite _ _ _
