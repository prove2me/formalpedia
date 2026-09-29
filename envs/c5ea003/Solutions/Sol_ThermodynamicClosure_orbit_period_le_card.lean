-- Prove2me | solution 1 for ThermodynamicClosure.orbit_period_le_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:15:54.511087+00:00
-- url     : https://prove2.me/submissions/c9098a0b-ba53-4191-abc5-ba253b6b205d

-- Sol generated from Speculative/AutoResearch/ThermodynamicClosureCore.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_ThermodynamicClosureCore

/-!
# Thermodynamic Closure Theory — Core Definitions and Foundational Theorems

## Overview

This file opens the field of **thermodynamic closure theory** by establishing that
closure operators on finite lattices carry intrinsic thermodynamic invariants related
to Landauer's principle, and that reversibility of computation is certifiable via
structural properties of closure operators.

**Bridge**: Connects order theory ↔ statistical mechanics ↔ reversible computation ↔
post-quantum cryptography.

## Main Results (20+ theorems, zero sorry)

* `landauer_defect_nonneg` — Defect ≥ 0 (Second Law).
* `closure_fiber_card_ge_two` — Non-fixed points have fiber ≥ 2.
* `landauer_defect_zero_implies_fixed` — Zero defect → fixed point.
* `landauer_defect_ge_one_of_nonfixed` — Non-fixed points have defect ≥ 1.
* `transition_closure_extensive` — Transition closures are extensive.
* `transition_closure_monotone` — Transition closures preserve order.
* `orbit_stabilizes_pigeonhole` — Orbits stabilize (pigeonhole).
* `entropy_closure_separation_strict` — Strict entropy increase.
* `bijective_orbit_periodic` — Bijective orbits are periodic.
* `monotone_extensive_convergence` — O(n) convergence bound.
* Plus many more.

## References

* Landauer, R. (1961). "Irreversibility and Heat Generation in the Computing Process"
-/

open Classical Function

noncomputable section

open ThermodynamicClosure

/-! ## Section 1: EML Closure Operator Structure -/




/-! ## Section 2: Basic Closure Properties -/





/-! ## Section 3: Thermodynamic Lattice Structure -/


variable {L : Type*}



/-! ## Section 4: Landauer Defect -/






/-
**Defect ≥ 1 at non-fixed points**: Non-trivial closure destroys
    at least one full bit. Uses closure_fiber_card_ge_two + log monotonicity.
    Bridge: minimum thermodynamic cost = k_B T ln 2 per bit.
-/




/-! ## Section 5: Transition Closure -/




/-! ## Section 6: Orbit Stabilization -/

/-
**Orbit stabilization (pigeonhole)**: ∃ m < n ≤ card L, f^m(x) = f^n(x).
    Bridge: computational orbits must cycle — finite systems reach steady state.
-/
theorem orbit_stabilizes_pigeonhole [Fintype L] [DecidableEq L]
    (f : L → L) (x : L) :
    ∃ m n : ℕ, m < n ∧ n ≤ Fintype.card L ∧ f^[m] x = f^[n] x := by
  obtain ⟨m, n, hmn, h_eq⟩ : ∃ m n : ℕ, m < n ∧ n ≤ Fintype.card L ∧ f^[m] x = f^[n] x := by
    have h_card : Fintype.card (Fin (Fintype.card L + 1)) > Fintype.card L := by
      exact Fintype.card_fin _ ▸ Nat.lt_succ_self _
    have h_pigeonhole : ∃ m n : Fin (Fintype.card L + 1), m ≠ n ∧ f^[m] x = f^[n] x := by
      contrapose! h_card;
      exact Fintype.card_le_of_injective ( fun m => f^[m] x ) fun m n hmn => Classical.not_not.1 fun hmn' => h_card m n hmn' hmn;
    obtain ⟨ m, n, hmn, h ⟩ := h_pigeonhole; cases lt_or_gt_of_ne hmn <;> [ exact ⟨ m, n, ‹_›, Nat.le_of_lt_succ ( Fin.is_lt _ ), h ⟩ ; exact ⟨ n, m, ‹_›, Nat.le_of_lt_succ ( Fin.is_lt _ ), h.symm ⟩ ] ;
  use m, n

/-! ## Section 7: Monotone Extensive Convergence -/

/-
**O(n) convergence**: A monotone extensive function on a finite partial order
    converges within card L steps.
    Bridge: thermodynamic relaxation has O(n) time complexity.
-/

/-! ## Section 8: Entropy and Closure -/







/-! ## Section 9: Closure Equivalence and Partition -/




/-! ## Section 10: Reversibility -/





/-! ## Section 11: Composition -/


/-! ## Section 12: Additional Orbit Theory -/

/-
**Orbit period bound**: Every orbit has period ≤ |L|.
    Bridge: O(n²) reversibility certification complexity.
-/


/-! ## Section 13: Landauer Defect and Entropy Interaction -/




/-! ## Section 14: Certified Robustness via Closure -/




open ThermodynamicClosure in
theorem solution    [Fintype L] [DecidableEq L]
    (f : L → L) (x : L) :
    ∃ p : ℕ, 0 < p ∧ p ≤ Fintype.card L ∧
      f^[p] (f^[Fintype.card L] x) = f^[Fintype.card L] x := by
  obtain ⟨ m, n, hmn, h ⟩ := orbit_stabilizes_pigeonhole f x;
  refine' ⟨ n - m, tsub_pos_of_lt hmn, _, _ ⟩;
  · exact le_trans ( Nat.sub_le _ _ ) h.1;
  · -- By induction on $k$, we can show that $f^{[m+k]} x = f^{[n+k]} x$ for all $k \geq 0$.
    have h_ind : ∀ k : ℕ, f^[m + k] x = f^[n + k] x := by
      intro k
      induction' k with k ih;
      · exact h.2;
      · rw [ Nat.add_succ, Nat.add_succ, Function.iterate_succ_apply', Function.iterate_succ_apply', ih ];
    convert h_ind ( Fintype.card L - m ) |> Eq.symm using 1;
    · rw [ ← Function.iterate_add_apply, add_comm, ← Nat.add_sub_assoc hmn.le ];
      rw [ show Fintype.card L + n - m = n + ( Fintype.card L - m ) by omega ];
    · rw [ Nat.add_sub_of_le ( hmn.le.trans h.1 ) ]
