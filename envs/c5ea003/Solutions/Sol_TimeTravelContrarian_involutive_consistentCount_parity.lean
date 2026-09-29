-- Prove2me | solution 1 for TimeTravelContrarian.involutive_consistentCount_parity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:13:10.350346+00:00
-- url     : https://prove2.me/submissions/ccd44506-1d7f-48d0-950b-3ccc0edaefa0

-- Sol generated from Novelty/TimeTravelContrarian.lean
import Mathlib
import Definitions.Def_Novelty_TimeTravelContrarian
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Time-Travel Logic, Contrarian Edition: which hypotheses *force* self-consistency?

This file continues the study of causal loops and the **Novikov self-consistency
principle** begun in `Catalog/.../TimeTravelCausalConsistency.lean`.  There a causal
loop's one-traversal net effect is modelled by a self-map `evolve : X → X`, and a loop
is **self-consistent** exactly when `evolve` has a fixed point.

The mission here is *contrarian*: we state a batch of bold conjectures of the form
"such-and-such structural hypothesis on the loop forces a consistent history", and for
each we either **prove** it or exhibit an explicit **counterexample** (a disproof).

The verdicts:

* `not_bijective_forces_selfConsistent` — **DISPROVED.**  Reversibility of the causal
  step (the loop map being a bijection) does *not* force self-consistency: the
  grandfather flip `¬·` on `Bool` is a bijection with no fixed point.
* `exists_sq_consistent_not_consistent` — **DISPROVED** ("consistency does not descend").
  A loop whose *double* traversal is self-consistent need not itself be self-consistent.
* `exists_selfConsistent_comp_not_selfConsistent` — **DISPROVED** ("consistency is not
  compositional").  Two self-consistent loops sharing a state space can compose to a
  fixed-point-free (paradoxical) loop; explicit witnesses on `Fin 3`.
* `selfConsistent_iterate` — **PROVED** ("consistency ascends").  A self-consistent
  loop stays self-consistent under every number of repetitions.
* `contracting_unique_selfConsistent` — **PROVED** ("deterministic time travel").  If
  the loop map is a contraction on a complete state space, the consistent history exists
  and is *unique* (Banach).
* `involutive_consistentCount_parity` — **PROVED** (quantitative Novikov).  For a
  reversible-by-symmetry (involutive) loop on a finite state space, the number of
  consistent histories has the same parity as the number of states.
* `involutive_odd_selfConsistent` — **PROVED** corollary: an involutive loop on an
  odd-sized state space is always self-consistent (with an *odd* number of histories).
* `exists_iterate_selfConsistent` — **PROVED** ("eventual consistency").  On a finite
  non-empty state space, some positive number of repetitions of *any* loop is
  self-consistent.
* `grandfather_consistentCount` / `identity_consistentCount` — concrete counts.
-/


open TimeTravelContrarian

open Function

variable {X : Type*}

/-! ## Core model -/





/-! ## Disproofs: hypotheses that do **not** force self-consistency -/




/-! ## Proofs: hypotheses that **do** force self-consistency -/



/-
**PROOF — quantitative Novikov for involutive loops.**  If the loop map is an
involution (traversing the loop twice restores the state) on a finite state space, then
the number of consistent histories has the *same parity* as the number of states.  This
refines the mere existence result below to an exact parity count.
-/


/-! ## Eventual consistency on finite state spaces -/



/-! ## Concrete counts -/




open TimeTravelContrarian in
theorem solution[Fintype X] [DecidableEq X] {f : X → X}
    (hf : Involutive f) :
    (CausalLoop.mk f).consistentCount ≡ Fintype.card X [MOD 2] := by
  -- Let σ be the permutation `Equiv.ofBijective f hf.bijective`.
  set σ : Equiv.Perm X := Equiv.ofBijective f ⟨Function.Involutive.injective hf, Function.Involutive.surjective hf⟩;
  -- By `Equiv.Perm.two_dvd_card_support`, the support of σ has even cardinality.
  have h_support_even : Even (Finset.card (σ.support)) := by
    convert Equiv.Perm.two_dvd_card_support ( show σ ^ 2 = 1 from ?_ ) using 1;
    · exact funext fun n => by simp +decide [ even_iff_two_dvd ] ;
    · ext x; simp +decide [ sq ] ;
      exact hf x;
  unfold CausalLoop.consistentCount; simp_all +decide [ Nat.ModEq, Nat.even_iff ] ;
  rw [ show Fintype.card X = Finset.card ( Finset.filter ( fun x => f x = x ) Finset.univ ) + Finset.card ( Finset.filter ( fun x => f x ≠ x ) Finset.univ ) by rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.2 fun _ _ _ => by tauto ), Finset.filter_union_filter_not_eq ] ; simp +decide, add_comm ];
  rw [ show Finset.filter ( fun x => f x ≠ x ) Finset.univ = σ.support from ?_ ] ; simp_all +decide [ Nat.add_mod ];
  ext x; simp [σ]
