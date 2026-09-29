-- Prove2me | solution 1 for MatroidMinorFiniteBasis.matroid_wqo_gives_finite_excluded_minors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:05:15.660762+00:00
-- url     : https://prove2.me/submissions/e0f8f6d3-47af-4bec-9da8-c6f20e8dcca8

-- Sol generated from Bridges/MatroidMinorFiniteBasis.lean
import Mathlib
import Definitions.Def_Bridges_MatroidMinorFiniteBasis
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Well-quasi-orders and finite excluded-minor bases

This file formalizes the order-theoretic implication at the heart of the proposed
Robertson--Seymour theorem for finite-field-representable matroids.  It does not
assert that representable matroids are well-quasi-ordered.  Instead, it proves
that any such well-quasi-order theorem would yield a finite excluded-minor
characterization.

The development applies to an arbitrary partial order, and is then stated in the
language of the matroid minor order.  The finite obstruction set is canonical:
it consists of the minimal objects outside the minor-closed class.
-/

open Set

open MatroidMinorFiniteBasis


variable {α : Type*} [PartialOrder α]


/-- Minimal members of a set are pairwise incomparable.
-/
theorem minimalMembers_isAntichain (U : Set α) :
    IsAntichain (· ≤ ·) (minimalMembers U) := by
  intro x hx y hy hxy;
  exact fun h => hy.2 x ( lt_of_le_of_ne h hxy ) hx.1

/-- A well-quasi-order has only finitely many minimal members in every set.
-/
theorem minimalMembers_finite
    (hwqo : WellQuasiOrdered ((· ≤ ·) : α → α → Prop)) (U : Set α) :
    (minimalMembers U).Finite := by
  -- By definition of a well-quasi-order, an antichain must be finite.
  have : IsAntichain (· ≤ ·) (minimalMembers U) := by
    apply minimalMembers_isAntichain;
  convert this.finite_of_wellQuasiOrdered hwqo

/-- Every member of a set in a well-quasi-order lies above a minimal member.
-/
theorem exists_minimalMember_le
    (hwqo : WellQuasiOrdered ((· ≤ ·) : α → α → Prop))
    (U : Set α) {x : α} (hx : x ∈ U) :
    ∃ b ∈ minimalMembers U, b ≤ x := by
  -- By the well-foundedness of <, there exists a minimal element g in the set {y | y ∈ U ∧ y ≤ x}.
  obtain ⟨g, hg⟩ : ∃ g ∈ {y | y ∈ U ∧ y ≤ x}, ∀ z ∈ {y | y ∈ U ∧ y ≤ x}, ¬z < g := by
    convert hwqo.wellFounded.has_min _ ?_;
    · simp +decide [lt_iff_le_and_ne];
      grind +qlia;
    · exact ⟨ x, hx, le_rfl ⟩;
  exact ⟨ g, ⟨ hg.1.1, fun z hz hz' => hg.2 z ⟨ hz', hz.le.trans hg.1.2 ⟩ hz ⟩, hg.1.2 ⟩

/-- A lower set in a well-quasi-order is characterized by finitely many canonical
minimal forbidden objects.
-/
theorem finite_canonical_forbidden_basis
    (hwqo : WellQuasiOrdered ((· ≤ ·) : α → α → Prop))
    (C : Set α) (hC : IsLowerSet C) :
    (minimalMembers Cᶜ).Finite ∧
      ∀ x, x ∈ C ↔ ∀ b ∈ minimalMembers Cᶜ, ¬ b ≤ x := by
  refine' ⟨ _, fun x => ⟨ fun hx b hb hb' => hb.1 <| hC hb' hx, _ ⟩ ⟩;
  · exact minimalMembers_finite hwqo Cᶜ
  · contrapose!;
    exact fun hx => exists_minimalMember_le hwqo ( Cᶜ ) hx







open Matroid

variable {α : Type*}



/-- Excluded minors are exactly the order-theoretic minimal members of the
complement.
-/
theorem isExcludedMinor_iff_minimalMember (C : Set (Matroid α)) (M : Matroid α) :
    IsExcludedMinor C M ↔ M ∈ minimalMembers Cᶜ := by
  -- By definition of `IsExcludedMinor`, we have that `M ∉ C` and `∀ ⦃N : Matroid α⦄, N <m M → N ∈ C`.
  simp [IsExcludedMinor, minimalMembers]







open MatroidMinorFiniteBasis in
theorem solution    (hwqo : WellQuasiOrdered ((· ≤m ·) : Matroid α → Matroid α → Prop))
    (C : Set (Matroid α)) (hC : IsMatroidMinorClosed C) :
    {M | IsExcludedMinor C M}.Finite ∧
      ∀ M, M ∈ C ↔ ∀ N, IsExcludedMinor C N → ¬ N ≤m M := by
  have h_lower_set : IsLowerSet C :=
    isLowerSet_iff_Iic_subset.mpr fun _ hM _ hNM => hC hM hNM
  convert finite_canonical_forbidden_basis hwqo C h_lower_set using 1;
  · rw [ show { M | IsExcludedMinor C M } = minimalMembers Cᶜ from ?_ ];
    exact Set.ext fun M => isExcludedMinor_iff_minimalMember C M;
  · simp +decide [ isExcludedMinor_iff_minimalMember ]
