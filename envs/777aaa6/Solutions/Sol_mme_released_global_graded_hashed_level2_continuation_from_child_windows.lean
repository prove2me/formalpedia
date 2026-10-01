-- Prove2me | solution 1 for mme_released_global_graded_hashed_level2_continuation_from_child_windows
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:54:43.969139+00:00
-- url     : https://prove2.me/submissions/cf46b38d-d38b-4ae8-aee1-c5b3d41ef63e

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_released_positive_integer_frame_data
import Definitions.Def_mme_regional_tolerance_window_data
import Theorems.Thm_mme_released_level2_pooled_positive_recipe
import Theorems.Thm_mme_released_level2_zero_half_boundary_recipe
import Theorems.Thm_mme_released_global_graded_hashed_level2_child_window_layout
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

namespace C7Level2

/-- The two-part index family `![A, B]` is the sum `Fin A ⊕ Fin B`. -/
def sigmaTwo (A B : ℕ) : ((j : Fin 2) × Fin (![A, B] j)) ≃ (Fin A ⊕ Fin B) where
  toFun p := Fin.cases (motive := fun j ↦ Fin (![A, B] j) → Fin A ⊕ Fin B) Sum.inl
      (fun j ↦ Fin.cases (motive := fun j : Fin 1 ↦ Fin (![A, B] j.succ) → Fin A ⊕ Fin B)
        Sum.inr (fun j ↦ j.elim0) j) p.1 p.2
  invFun := Sum.elim (fun q ↦ ⟨0, q⟩) (fun q ↦ ⟨1, q⟩)
  left_inv := by rintro ⟨j, q⟩; fin_cases j <;> rfl
  right_inv := by rintro (q | q) <;> rfl

/-- A two-part `partition` along a sum decomposition of the positions. -/
theorem partition_two {N ell A B : ℕ} {P : Predicate N} (pos : (Fin A ⊕ Fin B) ≃ Fin N)
    (Q0 : Predicate A) (Q1 : Predicate B)
    (inside : ∀ i x, Q0 i (fun q ↦ x (pos (Sum.inl q))) →
      Q1 i (fun q ↦ x (pos (Sum.inr q))) → P i x)
    (R0 : LogJointRecipeG A ell Q0) (R1 : LogJointRecipeG B ell Q1) :
    ∃ R : LogJointRecipeG N ell P, R.inputs = R0.inputs * R1.inputs ∧
      R.logOutputs = R0.logOutputs + R1.logOutputs ∧
      R.a * R.b * R.c = (R0.a * R0.b * R0.c) * (R1.a * R1.b * R1.c) := by
  let size : Fin 2 → ℕ := ![A, B]
  let Q : ∀ j, Predicate (size j) := Fin.cases (motive := fun j ↦ Predicate (size j)) Q0
    (fun j ↦ Fin.cases (motive := fun j : Fin 1 ↦ Predicate (size j.succ)) Q1
      (fun j ↦ j.elim0) j)
  let ch : ∀ j, LogJointRecipeG (size j) ell (Q j) :=
    Fin.cases (motive := fun j ↦ LogJointRecipeG (size j) ell (Q j)) R0
      (fun j ↦ Fin.cases (motive := fun j : Fin 1 ↦ LogJointRecipeG (size j.succ) ell (Q j.succ))
        R1 (fun j ↦ j.elim0) j)
  refine ⟨LogJointRecipeG.partition size ((sigmaTwo A B).trans pos) Q
    (fun i x hx ↦ inside i x (hx 0) (hx 1)) ch, ?_, ?_, ?_⟩
  · show ∏ j, (ch j).inputs = _
    rw [Fin.prod_univ_two]; rfl
  · show ∑ j, (ch j).logOutputs = _
    rw [Fin.sum_univ_two]; rfl
  · show (∏ j, (ch j).dims.1) * (∏ j, (ch j).dims.2.1) * (∏ j, (ch j).dims.2.2) = _
    rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
    show (R0.a * R1.a) * (R0.b * R1.b) * (R0.c * R1.c) = _
    ring

end C7Level2

open C7Level2 in
theorem solution :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ C : ℕ,
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∃ (a : ∀ o : Fin 6, Reference o (k^2))
          (frame : ∀ r : Fin 6, ReleasedPositiveInteger.Frame r (k^2)),
        ∀ E : ((r : Fin 6) × Fin (ReleasedJointInterior.blocks r (k^2) * 4)) ≃
            Fin (partSize (k^2) a 1),
        ∃ next : LogJointRecipeG (partSize (k^2) a 1) 2 (fun i y ↦ ∀ r : Fin 6,
            RecursiveYZ.Graded (RecStage.htotal3 r) ((ReleasedJointInterior.roleEquiv r).symm i)
              (frame r).reference
              (ProfiledCW.split (ell := 2) (frame r).positions
                (ReleasedJointInterior.positions_length r (k^2)) (fun q ↦ y (E ⟨r, q⟩))) ∧
            ∀ c w, |cellFrequency (RecursiveYZ.count (fullCell (RecStage.htotal3 r) (frame r).reference)
                (ProfiledCW.split (ell := 2) (frame r).positions
                  (ReleasedJointInterior.positions_length r (k^2)) (fun q ↦ y (E ⟨r, q⟩)))) c w -
              cellFrequency (fun c w ↦ k^2 * RecStage.mu3 r ((ReleasedJointInterior.roleEquiv r).symm i) c w) c w| ≤ δ),
          1 ≤ next.inputs ∧
          next.inputs ≤ (k + 1) ^ C ∧
          1 ≤ next.a * next.b * next.c ∧
          (6 * blocks (k^2) : ℝ) * ((5859676 : ℝ)/10000000) ≤ next.logOutputs ∧
          (6 * blocks (k^2) : ℝ) * ((583785872051 : ℝ)/100000000000) ≤
            Real.log ((next.a * next.b * next.c : ℕ) : ℝ) := by
  obtain ⟨C1, h1⟩ := mme_released_level2_pooled_positive_recipe
  obtain ⟨C2, h2⟩ := mme_released_level2_zero_half_boundary_recipe
  refine ⟨1, one_pos, fun δ hδ _ ↦ ?_⟩
  have h3 := mme_released_global_graded_hashed_level2_child_window_layout δ hδ
  refine ⟨2 * (C1 + C2), fun k0 ↦ ?_⟩
  have hsq : Filter.Tendsto (fun k : ℕ ↦ k ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num)
  obtain ⟨k, ⟨hR1, hR2, hlay⟩, hkk⟩ :=
    (((hsq.eventually h1).and ((hsq.eventually h2).and h3)).and
      (Filter.eventually_ge_atTop k0)).exists
  refine ⟨k, hkk, ?_⟩
  obtain ⟨a, frame, hE⟩ := hlay
  refine ⟨a, frame, fun E ↦ ?_⟩
  obtain ⟨L, zc, hzc, pos, hins⟩ := hE E
  obtain ⟨R1, i1, i1', d1, r1, dims1⟩ := hR1
  obtain ⟨R2, i2, i2', r2, d2, dims2⟩ := hR2 L zc hzc
  obtain ⟨R, hRin, hRout, hRdims⟩ := partition_two pos _ _ (fun i x hx0 hx1 ↦ hins i x hx0 hx1) R1 R2
  have hk2 : k ^ 2 + 1 ≤ (k + 1) ^ 2 := by nlinarith
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRin]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · rw [hRin]
    calc R1.inputs * R2.inputs ≤ (k ^ 2 + 1) ^ C1 * (k ^ 2 + 1) ^ C2 := Nat.mul_le_mul i1' i2'
      _ = (k ^ 2 + 1) ^ (C1 + C2) := by rw [pow_add]
      _ ≤ ((k + 1) ^ 2) ^ (C1 + C2) := Nat.pow_le_pow_left hk2 _
      _ = (k + 1) ^ (2 * (C1 + C2)) := by rw [← pow_mul]
  · rw [hRdims]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · rw [hRout]
    have hb : (6 * blocks (k ^ 2) : ℝ) * ((5859676 : ℝ) / 10000000) =
        ((5859676 * 6 * 10 ^ 53 : ℕ) : ℝ) * ((k ^ 2 : ℕ) : ℝ) := by
      simp only [blocks, MoreAsymmetryExactSeed.denominator]; push_cast; ring
    have hle : ((5859676 * 6 * 10 ^ 53 : ℕ) : ℝ) ≤ ((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ) := by
      norm_num
    have hk0 : (0 : ℝ) ≤ ((k ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hb]; nlinarith
  · rw [hRdims]
    have hx1 : (0 : ℝ) < ((R1.a * R1.b * R1.c : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hx2 : (0 : ℝ) < ((R2.a * R2.b * R2.c : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rw [Nat.cast_mul (R1.a * R1.b * R1.c), Real.log_mul hx1.ne' hx2.ne']
    have hb : (6 * blocks (k ^ 2) : ℝ) * ((583785872051 : ℝ) / 100000000000) =
        ((37468424 * 6 * 10 ^ 53 : ℕ) : ℝ) * ((k ^ 2 : ℕ) : ℝ) +
        ((209101632051 * 6 * 10 ^ 49 : ℕ) : ℝ) * ((k ^ 2 : ℕ) : ℝ) := by
      simp only [blocks, MoreAsymmetryExactSeed.denominator]; push_cast; ring
    rw [hb]; exact add_le_add dims1 dims2
