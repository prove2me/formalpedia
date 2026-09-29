-- Prove2me | Definitions.Def_Bridges_old_SupportTutteUniversality
-- name    : Bridges_old_SupportTutteUniversality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:54.10718+00:00
-- url     : https://prove2.me/theorems/eadf3768-80fb-402e-8201-c685f9ab72d5
-- title:
--   Aether Catalog definitions — Bridges_old_SupportTutteUniversality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.old.SupportTutteUniversality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/old/SupportTutteUniversality.lean by skeleton subtraction
import Mathlib
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

namespace SupportTutteUniversality

variable {ι : Type*} [DecidableEq ι]

/-! ## Section 1: Core Definitions -/

def sDelete (S : Finset (ι →₀ ℕ)) (i : ι) : Finset (ι →₀ ℕ) :=
  S.filter (fun m => m i = 0)

noncomputable def sContract (S : Finset (ι →₀ ℕ)) (i : ι) : Finset (ι →₀ ℕ) :=
  (S.filter (fun m => 0 < m i)).image (fun m => m - Finsupp.single i 1)

def IsSLoop (S : Finset (ι →₀ ℕ)) (i : ι) : Prop :=
  ∀ m ∈ S, m i > 0

def IsOrdCoord (S : Finset (ι →₀ ℕ)) (i : ι) : Prop :=
  (∃ m ∈ S, m i = 0) ∧ (∃ m ∈ S, 0 < m i)

noncomputable def sTotalDeg (S : Finset (ι →₀ ℕ)) : ℕ :=
  S.sum (fun m => m.sum (fun _ v => v))

noncomputable def sMeasure (S : Finset (ι →₀ ℕ)) : ℕ :=
  sTotalDeg S + S.card

def IsBinarySupport (S : Finset (ι →₀ ℕ)) : Prop :=
  ∀ m ∈ S, ∀ i : ι, m i = 0 ∨ m i = 1

/-! ## Section 2: Basic Lemmas -/

theorem sDelete_subset (S : Finset (ι →₀ ℕ)) (i : ι) :
    sDelete S i ⊆ S :=
  filter_subset _ _

theorem mem_sDelete_iff {S : Finset (ι →₀ ℕ)} {i : ι} {m : ι →₀ ℕ} :
    m ∈ sDelete S i ↔ m ∈ S ∧ m i = 0 :=
  Finset.mem_filter

theorem sDelete_card_lt {S : Finset (ι →₀ ℕ)} {i : ι}
    (h : ∃ m ∈ S, 0 < m i) :
    (sDelete S i).card < S.card := by
  apply Finset.card_lt_card
  exact ⟨sDelete_subset S i, fun heq => by
    obtain ⟨m, hm, hmi⟩ := h
    have := heq hm; rw [mem_sDelete_iff] at this; omega⟩

theorem sContract_card_le (S : Finset (ι →₀ ℕ)) (i : ι) :
    (sContract S i).card ≤ S.card :=
  le_trans Finset.card_image_le (Finset.card_filter_le _ _)

omit [DecidableEq ι] in
theorem sTotalDeg_mono {S T : Finset (ι →₀ ℕ)} (h : S ⊆ T) :
    sTotalDeg S ≤ sTotalDeg T :=
  Finset.sum_le_sum_of_subset h

theorem sMeasure_delete_lt {S : Finset (ι →₀ ℕ)} {i : ι}
    (h : ∃ m ∈ S, 0 < m i) :
    sMeasure (sDelete S i) < sMeasure S := by
  unfold sMeasure
  have h1 := sTotalDeg_mono (sDelete_subset S i)
  have h2 := sDelete_card_lt h
  omega

theorem sContract_card_lt_of_ordinary {S : Finset (ι →₀ ℕ)} {i : ι}
    (hzero : ∃ m ∈ S, m i = 0) (hpos : ∃ m ∈ S, 0 < m i) :
    (sContract S i).card < S.card := by
  calc (sContract S i).card
      ≤ (S.filter (fun m => 0 < m i)).card := Finset.card_image_le
    _ < S.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
        obtain ⟨m, hm, hmi⟩ := hzero
        have := h hm; simp [Finset.mem_filter] at this; omega

/-! ## Section 3: Measure Descent -/

theorem sTotalDeg_sContract_le (S : Finset (ι →₀ ℕ)) (i : ι) :
    sTotalDeg (sContract S i) ≤ sTotalDeg S := by
  unfold sContract sTotalDeg;
  rw [ Finset.sum_image ];
  · refine' le_trans ( Finset.sum_le_sum_of_subset ( Finset.filter_subset _ _ ) ) ( Finset.sum_le_sum fun x hx => _ );
    rw [ Finsupp.sum_of_support_subset ];
    case s => exact x.support;
    · exact Finset.sum_le_sum fun j hj => by by_cases h : j = i <;> simp +decide [ h ] ;
    · intro j hj; contrapose! hj; aesop;
    · exact fun _ _ => rfl;
  · intro m hm m' hm' h; simp_all +decide [ Finsupp.ext_iff ] ;
    intro a; specialize h a; by_cases ha : a = i <;> simp_all +decide [ Finsupp.single_apply ] ; omega;

theorem sMeasure_contract_lt_of_ordinary {S : Finset (ι →₀ ℕ)} {i : ι}
    (hord : IsOrdCoord S i) :
    sMeasure (sContract S i) < sMeasure S := by
  unfold sMeasure
  have h1 := sTotalDeg_sContract_le S i
  have h2 := sContract_card_lt_of_ordinary hord.1 hord.2
  omega

theorem sMeasure_contract_lt_of_loop {S : Finset (ι →₀ ℕ)} {i : ι}
    (hloop : IsSLoop S i) (hne : S.Nonempty) :
    sMeasure (sContract S i) < sMeasure S := by
  -- Since i is a loop, every m ∈ S has m i > 0. The filter (fun m => 0 < m i) equals S itself. The contraction map subtracts 1 from coordinate i, so each element loses at least 1 from total degree.
  have h_total_deg : sTotalDeg (sContract S i) ≤ sTotalDeg S - S.card := by
    refine' Nat.le_sub_of_add_le _;
    have h_total_deg : ∀ m ∈ S, (m - Finsupp.single i 1).sum (fun _ v => v) + 1 ≤ m.sum (fun _ v => v) := by
      intro m hm; specialize hloop m hm; simp_all +decide [ Finsupp.sum_fintype ] ;
      rw [ Finsupp.sum_of_support_subset ];
      case s => exact m.support;
      · refine' Finset.sum_lt_sum _ _ <;> simp_all +decide [ Finsupp.single_apply ];
        grind +qlia;
      · intro j hj; contrapose! hj; aesop;
      · exact fun _ _ => rfl;
    convert Finset.sum_le_sum h_total_deg using 1;
    unfold sTotalDeg sContract;
    rw [ Finset.sum_add_distrib, Finset.sum_image ];
    · rw [ Finset.filter_true_of_mem fun x hx => hloop x hx ] ; simp +decide;
    · intro m hm m' hm' h; simp_all +decide [ Finsupp.ext_iff ] ;
      intro a; specialize h a; by_cases ha : a = i <;> simp_all +decide [ Finsupp.single_apply ] ;
      omega;
  refine' lt_of_le_of_lt ( add_le_add h_total_deg ( sContract_card_le S i ) ) _;
  rw [ tsub_add_cancel_of_le ] <;> norm_num [ sMeasure ];
  · exact hne;
  · refine' le_trans _ ( Finset.sum_le_sum fun m hm => show m.sum ( fun _ v => v ) ≥ 1 from _ );
    · simp +decide;
    · exact le_trans ( Nat.succ_le_of_lt ( hloop m hm ) ) ( Finset.single_le_sum ( fun a _ => Nat.zero_le ( m a ) ) ( Finsupp.mem_support_iff.mpr ( ne_of_gt ( hloop m hm ) ) ) )

/-! ## Section 4: Support Classification -/


/-! ## Section 5: Canonical Evaluation -/

noncomputable def canonicalSupportEval {R : Type*} [CommSemiring R]
    (xL : R) (S : Finset (ι →₀ ℕ)) : R :=
  if _h₁ : S = ∅ then 1
  else if _h₂ : S = {0} then 1
  else if h₃ : ∃ i, IsOrdCoord S i then
    have : sMeasure (sDelete S h₃.choose) < sMeasure S :=
      sMeasure_delete_lt h₃.choose_spec.2
    have : sMeasure (sContract S h₃.choose) < sMeasure S :=
      sMeasure_contract_lt_of_ordinary h₃.choose_spec
    canonicalSupportEval xL (sDelete S h₃.choose) +
      canonicalSupportEval xL (sContract S h₃.choose)
  else if h₄ : ∃ i, IsSLoop S i then
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr _h₁
    have : sMeasure (sContract S h₄.choose) < sMeasure S :=
      sMeasure_contract_lt_of_loop h₄.choose_spec hne
    xL * canonicalSupportEval xL (sContract S h₄.choose)
  else 1
termination_by sMeasure S

/-! ## Section 6: Theorem A — Base Cases -/



/-! ## Section 7: Theorem C — Universal Factorization -/


/-! ## Section 8: Uniqueness Corollary -/


/-! ## Section 9: Partition and Cardinality -/




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

/-- **Support activity data** for deletion–contraction decomposition. -/
structure SupportActivityData where
  loops : ℕ
  coloops : ℕ
  ordinaryDel : ℕ
  ordinaryCon : ℕ
  deriving Repr, DecidableEq


noncomputable def loopCount (S : Finset (ι →₀ ℕ)) (ground : Finset ι) : ℕ :=
  (ground.filter (fun i => ∀ m ∈ S, 0 < m i)).card

noncomputable def ordinaryCount (S : Finset (ι →₀ ℕ)) (ground : Finset ι) : ℕ :=
  (ground.filter (fun i => (∃ m ∈ S, m i = 0) ∧ (∃ m ∈ S, 0 < m i))).card

noncomputable def trivialCount (S : Finset (ι →₀ ℕ)) (ground : Finset ι) : ℕ :=
  (ground.filter (fun i => ∀ m ∈ S, m i = 0)).card

/-
**Activity partition theorem.** Coordinates partition into loops,
    ordinary, and trivial, so their counts sum to `|ground|`.
-/

end SupportTutteUniversality


