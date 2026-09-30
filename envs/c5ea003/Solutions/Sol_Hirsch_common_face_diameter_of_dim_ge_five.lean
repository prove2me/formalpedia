-- Prove2me | solution 1 for Hirsch.common_face_diameter_of_dim_ge_five
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T03:30:19.519912+00:00
-- url     : https://prove2.me/submissions/3f31b1aa-7ac8-484c-938c-1fc6a3cc7ca8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Hirsch_common_face_diameter_of_dim_eq_five
import Theorems.Thm_Hirsch_common_face_diameter_of_dim_ge_six

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
open Set Hirsch HirschCommonFace

theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {m L : ℕ} (h : m ≤ L) (hP : DiamLE P m) : DiamLE P L := by
  intro u hu v hv
  obtain ⟨w, hw0, hwm, hs⟩ := hP u hu v hv
  refine ⟨fun i => w (min i m), ?_, ?_, ?_⟩
  · simp [hw0]
  · simp [min_eq_right h, hwm]
  · intro i hi
    by_cases h1 : i + 1 ≤ m
    · have hi' : i < m := Nat.lt_of_succ_le h1
      have hmin_i : min i m = i := min_eq_left (Nat.le_of_lt hi')
      have hmin_i1 : min (i + 1) m = i + 1 := min_eq_left h1
      simpa [hmin_i, hmin_i1] using hs i hi'
    · have hmi : min i m = m := by omega
      have hmi1 : min (i + 1) m = m := by omega
      exact Or.inl (by simp [hmi, hmi1])

theorem solution :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
      (u x : EuclideanSpace ℝ (Fin d)),
      Bornology.IsBounded (Hpoly a b) →
      5 ≤ HirschCommonFace.commonFaceDim a b u x →
      (HirschCommonFace.commonFace a b u x).Nonempty →
      DiamLE (HirschCommonFace.commonFace a b u x) (C * (n + d) ^ k) := by
  obtain ⟨C6, k6, h6⟩ := Hirsch.common_face_diameter_of_dim_ge_six
  refine ⟨max 4 C6, max 1 k6, ?_⟩
  intro d n a b u x hbd hdim hne
  have hle_d : commonFaceDim a b u x ≤ d := by
    simpa [commonFaceDim] using Submodule.finrank_le (commonDirection a b u x)
  have hpos : 0 < n + d := by omega
  by_cases h5 : commonFaceDim a b u x = 5
  · have hraw := common_face_diameter_of_dim_eq_five a b u x hbd hne h5
    have hle : 4 * n ≤ max 4 C6 * (n + d) ^ max 1 k6 := by
      have hn : 4 * n ≤ 4 * (n + d) := Nat.mul_le_mul_left 4 (Nat.le_add_right n d)
      have hC : 4 ≤ max 4 C6 := Nat.le_max_left _ _
      have hk : 1 ≤ max 1 k6 := Nat.le_max_left _ _
      have hpow : n + d ≤ (n + d) ^ max 1 k6 :=
        Nat.le_self_pow (Nat.ne_of_gt (Nat.succ_le_iff.mp hk)) (n + d)
      have : 4 * (n + d) ≤ max 4 C6 * (n + d) ^ max 1 k6 :=
        (Nat.mul_le_mul_right (n + d) hC).trans (Nat.mul_le_mul_left _ hpow)
      exact hn.trans this
    exact diamLE_mono _ hle hraw
  · have hge : 6 ≤ commonFaceDim a b u x := by omega
    have hraw := h6 d n a b u x hbd hge hne
    have hle : C6 * (n + d) ^ k6 ≤ max 4 C6 * (n + d) ^ max 1 k6 :=
      Nat.mul_le_mul (Nat.le_max_right _ _)
        (Nat.pow_le_pow_right hpos (Nat.le_max_right _ _))
    exact diamLE_mono _ hle hraw

#print axioms solution
