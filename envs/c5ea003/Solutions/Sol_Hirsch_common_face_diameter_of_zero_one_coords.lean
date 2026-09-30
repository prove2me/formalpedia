-- Prove2me | solution 1 for Hirsch.common_face_diameter_of_zero_one_coords
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T06:52:29.268984+00:00
-- url     : https://prove2.me/submissions/6f4764dc-e8c9-4643-a0ab-27de44853c76

import Theorems.Thm_Hirsch_zero_one_polytope_diameter_le_dimension
import Theorems.Thm_Hirsch_common_face_diamLE_of_coord_diamLE
import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped RealInnerProductSpace InnerProduct
open Set Hirsch HirschCommonFace

noncomputable section

variable {d n : ℕ}

theorem mem_commonFace_iff_sub_mem_commonDirection
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x y : EuclideanSpace ℝ (Fin d)) :
    y ∈ commonFace a b u x ↔
      y ∈ Hpoly a b ∧ y - u ∈ commonDirection a b u x := by
  constructor
  · intro hy
    refine ⟨hy.1, ?_⟩
    rw [commonDirection, LinearMap.mem_ker]
    funext ii
    have hiC : ii.1 ∈ commonSourceRows a b u x := ii.2
    have hyi : ⟪a ii.1, y⟫ = b ii.1 := hy.2 ii.1 hiC
    have hui : ⟪a ii.1, u⟫ = b ii.1 :=
      (Finset.mem_filter.1 hiC).2.2.1
    change ⟪a ii.1, y - u⟫ = 0
    rw [inner_sub_right, hyi, hui]
    ring
  · rintro ⟨hyP, hdir⟩
    refine ⟨hyP, ?_⟩
    intro i hiC
    have hker : rowEvalMap a (commonSourceRows a b u x) (y - u) = 0 :=
      LinearMap.mem_ker.1 hdir
    have hcoord : ⟪a i, y - u⟫ = 0 := by
      change (rowEvalMap a (commonSourceRows a b u x) (y - u)) ⟨i, hiC⟩ = 0
      exact congrFun hker ⟨i, hiC⟩
    have hui : ⟪a i, u⟫ = b i :=
      (Finset.mem_filter.1 hiC).2.2.1
    rw [inner_sub_right, hui] at hcoord
    linarith

theorem commonFace_inner_restricted
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (i : Fin n) (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    ⟪commonFaceA a b u x i, q⟫ =
      ⟪a i, commonFaceLift a b u x q⟫ := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (commonFaceLiftCLM a b u x) q (a i)
  simpa [commonFaceA, commonFaceLiftCLM, real_inner_comm] using h

theorem commonFaceLift_mem_direction
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    commonFaceLift a b u x q ∈ commonDirection a b u x := by
  change (((commonFaceRepr a b u x).symm q : commonDirection a b u x) :
    EuclideanSpace ℝ (Fin d)) ∈ commonDirection a b u x
  exact ((commonFaceRepr a b u x).symm q).property

theorem commonFacePoint_sub
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    commonFacePoint a b u x q - u = commonFaceLift a b u x q := by
  simp [commonFacePoint]

theorem mem_commonFace_coord_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    q ∈ Hpoly (commonFaceA a b u x) (commonFaceB a b u x) ↔
      commonFacePoint a b u x q ∈ commonFace a b u x := by
  rw [mem_commonFace_iff_sub_mem_commonDirection]
  constructor
  · intro hq
    refine ⟨?_, ?_⟩
    · intro i
      have hi := hq i
      rw [commonFace_inner_restricted] at hi
      dsimp [commonFaceB] at hi
      dsimp [commonFacePoint]
      rw [inner_add_right]
      linarith
    · rw [commonFacePoint_sub]
      exact commonFaceLift_mem_direction a b u x q
  · rintro ⟨hp, _hdir⟩
    intro i
    have hi := hp i
    rw [commonFace_inner_restricted]
    dsimp [commonFaceB, commonFacePoint] at hi ⊢
    rw [inner_add_right] at hi
    linarith

theorem commonFace_coord_bounded
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    Bornology.IsBounded
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) := by
  obtain ⟨C, hC⟩ := hbd.exists_norm_le
  refine (isBounded_iff_forall_norm_le).2
    ⟨max 0 (C + ‖u‖), fun q hq => ?_⟩
  have hpF := (mem_commonFace_coord_iff a b u x q).1 hq
  have hp : commonFacePoint a b u x q ∈ Hpoly a b := hpF.1
  have hCp := hC _ hp
  have hlift : ‖commonFaceLift a b u x q‖ = ‖q‖ :=
    (commonFaceLift a b u x).norm_map q
  have htri : ‖commonFaceLift a b u x q‖ ≤
      ‖commonFacePoint a b u x q‖ + ‖u‖ := by
    have h := norm_sub_le (commonFacePoint a b u x q) u
    simpa [commonFacePoint] using h
  have hmain : ‖q‖ ≤ C + ‖u‖ := by
    rw [← hlift]
    linarith
  exact hmain.trans (le_max_right _ _)

theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (h01 : ∀ q ∈ extremePoints ℝ
        (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)),
      ∀ i : Fin (commonFaceDim a b u x), q i = 0 ∨ q i = 1) :
    DiamLE (commonFace a b u x) (commonFaceDim a b u x) := by
  have hbdQ := commonFace_coord_bounded a b u x hbd
  have hcoord :=
    zero_one_polytope_diameter_le_dimension
      (commonFaceA a b u x) (commonFaceB a b u x) hbdQ h01
  exact common_face_diamLE_of_coord_diamLE a b u x hcoord

#print axioms solution
