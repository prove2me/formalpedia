-- Prove2me | solution 2 for BrunnMinkowski1D.brunn_minkowski_1d
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T14:35:45.621295+00:00
-- url     : https://prove2.me/submissions/a55c6195-80e6-40bf-969e-4dbdd7312245

-- Sol generated from Geometry/Brunnminkowski1d/BrunnMinkowski1D.lean
import Mathlib

open MeasureTheory Set
open scoped Pointwise


/-
Translating a set by a singleton on the right preserves Lebesgue volume.
-/
lemma translate_volume (A : Set ℝ) (b : ℝ) : volume (A + {b}) = volume A := by
  simp +decide [ Set.add_singleton, Set.image_add_right ]

/-
Translating a set by a singleton on the left preserves Lebesgue volume.
-/
lemma translate_volume' (B : Set ℝ) (a : ℝ) : volume ({a} + B) = volume B := by
  rw [ ← MeasureTheory.measure_preimage_add_right ];
  swap;
  exact a;
  simp +decide [ Set.preimage, Set.mem_add ]

/-
`A + {b} ⊆ A + B` when `b ∈ B`.
-/
lemma subset_left {A B : Set ℝ} {b : ℝ} (hb : b ∈ B) : A + {b} ⊆ A + B := by
  exact Set.add_subset_add Set.Subset.rfl ( Set.singleton_subset_iff.mpr hb )

/-
`{a} + B ⊆ A + B` when `a ∈ A`.
-/
lemma subset_right {A B : Set ℝ} {a : ℝ} (ha : a ∈ A) : {a} + B ⊆ A + B := by
  exact Set.add_subset_add ( Set.singleton_subset_iff.mpr ha ) ( Set.Subset.refl _ )

/-
The intersection of the two translates is contained in a single point.
-/
lemma inter_singleton_bound {A B : Set ℝ} {a b : ℝ} (ha : a = sSup A) (hb : b = sInf B)
    (hA : IsCompact A) (hAnon : A.Nonempty) (hB : IsCompact B) (hBnon : B.Nonempty) :
    (A + {b}) ∩ ({a} + B) ⊆ {a + b} := by
  intro x;
  simp +zetaDelta at *;
  exact fun hx₁ hx₂ => by linarith [ ha ▸ le_csSup ( hA.bddAbove ) hx₁, hb ▸ csInf_le ( hB.bddBelow ) hx₂ ] ;

/-
The one-dimensional Brunn–Minkowski inequality.
-/


theorem solution{A B : Set ℝ} (hA : IsCompact A) (hAnon : A.Nonempty)
    (hB : IsCompact B) (hBnon : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a, ha⟩ : ∃ a, a = sSup A ∧ a ∈ A := by
    exact ⟨ _, rfl, hA.sSup_mem hAnon ⟩
  obtain ⟨b, hb⟩ : ∃ b, b = sInf B ∧ b ∈ B := by
    exact ⟨ _, rfl, hB.sInf_mem hBnon ⟩
  set U := A + {b}
  set V := {a} + B
  have hUV : U ∪ V ⊆ A + B := by
    exact Set.union_subset ( subset_left hb.2 ) ( subset_right ha.2 )
  have hUV_inter : U ∩ V ⊆ {a + b} := by
    apply inter_singleton_bound ha.left hb.left hA hAnon hB hBnon
  have hUV_union : volume (U ∪ V) + volume (U ∩ V) = volume U + volume V := by
    apply MeasureTheory.measure_union_add_inter;
    exact IsCompact.measurableSet ( isCompact_singleton.add hB )
  have hUV_le : volume U + volume V ≤ volume (U ∪ V) + volume (U ∩ V) := by
    rw [hUV_union];
  convert hUV_le.trans ( add_le_add ( MeasureTheory.measure_mono hUV ) ( MeasureTheory.measure_mono hUV_inter ) ) using 1;
  · rw [ translate_volume, translate_volume' ];
  · norm_num
