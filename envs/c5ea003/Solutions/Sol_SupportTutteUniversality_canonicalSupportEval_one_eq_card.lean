-- Prove2me | solution 1 for SupportTutteUniversality.canonicalSupportEval_one_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:01:04.596216+00:00
-- url     : https://prove2.me/submissions/96fa3883-fc34-4bde-8a5e-300c6df7c6f1

-- Sol generated from Bridges/old/SupportTutteUniversality.lean
import Mathlib
import Definitions.Def_Bridges_old_SupportTutteUniversality
import Theorems.Thm_SupportTutteUniversality_dc_invariant_factors_through_canonical
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Universal Support-Tutte Invariant: Full Universality and Cross-Domain Bridge

This file establishes the **universal factorization theorem** for
deletion–contraction invariants on M-convex supports, proves a cardinality
specialization, and provides a cross-domain bridge to matroid theory via
binary supports.

## Main Results

* `dc_invariant_factors_through_canonical` — Universal factorization (Theorem C)
* `dc_invariant_unique` — Uniqueness corollary (uses multi-step calc)
* `canonicalSupportEval_one_eq_card` — Cardinality specialization (Theorem B)
* `activity_partition` — Activity counting theorem
* `binary_support_card_recursion` — Bridge to matroid theory (Theorem D)

## References

* Murota, "Discrete Convex Analysis", SIAM, 2003
* Brylawski–Oxley, "The Tutte polynomial and its applications", 1992
-/

open Finset BigOperators Finsupp

attribute [local instance] Classical.propDecidable

open SupportTutteUniversality

variable {ι : Type*} [DecidableEq ι]

/-! ## Section 1: Core Definitions -/








/-! ## Section 2: Basic Lemmas -/








/-! ## Section 3: Measure Descent -/




/-! ## Section 4: Support Classification -/


/-! ## Section 5: Canonical Evaluation -/


/-! ## Section 6: Theorem A — Base Cases -/



/-! ## Section 7: Theorem C — Universal Factorization -/


/-! ## Section 8: Uniqueness Corollary -/


/-! ## Section 9: Partition and Cardinality -/

theorem sContract_card_eq_filter (S : Finset (ι →₀ ℕ)) (i : ι) :
    (sContract S i).card = (S.filter (fun m => 0 < m i)).card := by
  rw [ sContract, Finset.card_image_of_injOn ];
  intro m hm n hn hmn; ext j; replace hmn := congr_arg ( fun f => f j ) hmn; by_cases hj : j = i <;> simp_all +decide [ Finsupp.single_apply ] ;
  omega

theorem delete_contract_card_partition (S : Finset (ι →₀ ℕ)) (i : ι) :
    (sDelete S i).card + (sContract S i).card = S.card := by
  rw [ sContract_card_eq_filter, ← Finset.card_union_of_disjoint ];
  · congr with m ; by_cases hm : m i = 0 <;> simp +decide [ hm, sDelete ];
    exact fun _ => Nat.pos_of_ne_zero hm;
  · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;

theorem sContract_card_eq_of_loop {S : Finset (ι →₀ ℕ)} {i : ι}
    (hloop : IsSLoop S i) :
    (sContract S i).card = S.card := by
  convert sContract_card_eq_filter S i using 1;
  rw [ Finset.filter_true_of_mem hloop ]

/-! ## Section 10: Theorem B — Cardinality Specialization -/

/-
**Theorem B (Cardinality specialization).**
    Evaluating at `xL = 1` recovers the support cardinality.
-/

/-! ## Section 11: Theorem D — Binary Support Bridge -/

/-
For binary supports, ordinary coordinates correspond exactly to
    having both 0-valued and 1-valued elements.
-/


/-
Binary support contraction produces binary support.
-/



/-! ## Section 12: Activity Counting -/






/-
**Activity partition theorem.** Coordinates partition into loops,
    ordinary, and trivial, so their counts sum to `|ground|`.
-/


open SupportTutteUniversality in
theorem solution    (S : Finset (ι →₀ ℕ)) (hne : S.Nonempty) :
    canonicalSupportEval (1 : ℕ) S = S.card := by
  convert dc_invariant_factors_through_canonical 1 ( fun T => if T = ∅ then 1 else T.card ) _ _ _ _ using 1;
  any_goals tauto;
  · constructor;
    · intro h S;
      apply Eq.symm; exact (by
        have := dc_invariant_factors_through_canonical 1 (fun T => if T = ∅ then 1 else T.card) (by
        simp +decide) (by
        simp +decide) (by
        intro S i hi; have := delete_contract_card_partition S i; simp_all +decide ;
        split_ifs <;> simp_all +decide [ IsOrdCoord ];
        · exact absurd this ( ne_of_lt ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ‹_› ) ) );
        · simp_all +decide [ Finset.ext_iff, sDelete ];
          exact absurd hi.1 ( by tauto );
        · unfold sContract at *; aesop;) (by
        intro S i hi hne; simp +decide [ hi, hne, sContract_card_eq_of_loop hi ] ;
        rw [ if_neg ( Finset.Nonempty.ne_empty hne ), if_neg ( Finset.Nonempty.ne_empty ( Finset.card_pos.mp ( by rw [ sContract_card_eq_of_loop hi ] ; exact Finset.card_pos.mpr hne ) ) ) ]) S;
        exact this.symm
      );
    · grind;
  · intro S i hi; by_cases hS : S = ∅ <;> simp +decide [ hS, delete_contract_card_partition ] ;
    · cases hi ; aesop;
    · split_ifs <;> simp_all +decide [ IsOrdCoord ];
      · simp_all +decide [ sDelete, sContract ];
      · simp_all +decide [ sDelete ];
        grind;
      · unfold sContract at *; aesop;
      · rw [ delete_contract_card_partition ];
  · intro S i hloop hne; simp +decide [ hloop, hne, sContract_card_eq_of_loop ] ;
    simp +decide [ sContract, hne.ne_empty ];
    exact fun h => absurd ( hloop _ hne.choose_spec ) ( by simp +decide [ h hne.choose_spec ] )
