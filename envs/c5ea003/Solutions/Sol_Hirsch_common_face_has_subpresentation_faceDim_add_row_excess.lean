-- Prove2me | solution 1 for Hirsch.common_face_has_subpresentation_faceDim_add_row_excess
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T19:02:55.685214+00:00
-- url     : https://prove2.me/submissions/e5829063-8890-484e-a67f-9a70c920ee2c

import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
open scoped RealInnerProductSpace InnerProduct
open Set Module Hirsch


open scoped RealInnerProductSpace InnerProduct
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschRowExcessPublic

private lemma commonFace_inner_restricted {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (i : Fin n)
    (q : EuclideanSpace ℝ (Fin (HirschCommonFace.commonFaceDim a b u v))) :
    ⟪HirschCommonFace.commonFaceA a b u v i, q⟫ =
      ⟪a i, HirschCommonFace.commonFaceLift a b u v q⟫ := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (HirschCommonFace.commonFaceLiftCLM a b u v) q (a i)
  simpa [HirschCommonFace.commonFaceA, HirschCommonFace.commonFaceLiftCLM,
    real_inner_comm] using h

private lemma commonFaceLift_mem_direction {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (HirschCommonFace.commonFaceDim a b u v))) :
    HirschCommonFace.commonFaceLift a b u v q ∈
      HirschCommonFace.commonDirection a b u v := by
  change (((HirschCommonFace.commonFaceRepr a b u v).symm q :
    HirschCommonFace.commonDirection a b u v) :
      EuclideanSpace ℝ (Fin d)) ∈ HirschCommonFace.commonDirection a b u v
  exact ((HirschCommonFace.commonFaceRepr a b u v).symm q).property

private lemma commonFaceA_eq_zero_of_commonSourceRow {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hi : i ∈ HirschCommonFace.commonSourceRows a b u v) :
    HirschCommonFace.commonFaceA a b u v i = 0 := by
  rw [← @inner_self_eq_zero ℝ]
  rw [commonFace_inner_restricted]
  let q := HirschCommonFace.commonFaceA a b u v i
  have hmem := commonFaceLift_mem_direction a b u v q
  have hker :
      HirschCommonFace.rowEvalMap a (HirschCommonFace.commonSourceRows a b u v)
          (HirschCommonFace.commonFaceLift a b u v q) = 0 := by
    apply LinearMap.mem_ker.mp
    simpa [HirschCommonFace.commonDirection] using hmem
  have hcoord := congrFun hker ⟨i, hi⟩
  simpa [HirschCommonFace.rowEvalMap] using hcoord

/-- Restricting to a common carrier cannot increase row-presentation excess.
More precisely, if `d ≤ n` and the source checkpoint is feasible, then the
canonical common-face coordinate H-polyhedron has an equivalent original-row
subpresentation using at most `h + (n-d)` rows. No boundedness, circuit, or
endpoint-vertex assumption is needed. -/
theorem common_face_has_subpresentation_faceDim_add_row_excess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (hdn : d ≤ n) :
    HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v
      (HirschCommonFace.commonFaceDim a b u v + (n - d)) := by
  classical
  let A := HirschCommonFace.commonFaceA a b u v
  let B := HirschCommonFace.commonFaceB a b u v
  let C := HirschCommonFace.commonSourceRows a b u v
  let F : Finset (Fin n) := Finset.univ.filter (fun i => A i ≠ 0)
  have hzero :
      (0 : EuclideanSpace ℝ (Fin (HirschCommonFace.commonFaceDim a b u v))) ∈
        Hpoly A B := by
    intro i
    dsimp [A, B]
    simp only [inner_zero_right]
    exact sub_nonneg.mpr (hu i)
  have hdis : Disjoint C F := by
    apply Finset.disjoint_left.mpr
    intro i hiC hiF
    have hAi : A i = 0 := by
      simpa [A, C] using commonFaceA_eq_zero_of_commonSourceRow a b u v i hiC
    have hne : A i ≠ 0 := by simpa [F] using hiF
    exact hne hAi
  let T := HirschCommonFace.rowEvalMap a C
  let W := HirschCommonFace.commonDirection a b u v
  have hnull : Module.finrank ℝ T.range + Module.finrank ℝ W = d := by
    have h := T.finrank_range_add_finrank_ker
    have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    rw [hdom] at h
    simpa [T, W, C, HirschCommonFace.commonDirection] using h
  have hrange : Module.finrank ℝ T.range ≤ C.card := by
    calc
      Module.finrank ℝ T.range ≤ Module.finrank ℝ (C → ℝ) :=
        Submodule.finrank_le _
      _ = C.card := by simp [Fintype.card_coe]
  have htotal : C.card + F.card ≤ n := by
    have hcard : (C ∪ F).card = C.card + F.card :=
      Finset.card_union_of_disjoint hdis
    have hle := Finset.card_le_card (Finset.subset_univ (C ∪ F))
    rw [hcard] at hle
    simpa using hle
  have hFle : F.card ≤ HirschCommonFace.commonFaceDim a b u v + (n - d) := by
    have hdimW : Module.finrank ℝ W = HirschCommonFace.commonFaceDim a b u v := by
      rfl
    omega
  let q : Fin F.card ≃ {i : Fin n // i ∈ F} :=
    (Fintype.equivFinOfCardEq (α := {i : Fin n // i ∈ F}) (by simp)).symm
  let eF : Fin F.card ↪ Fin n :=
    ⟨fun j => (q j).1, by
      intro j k hjk
      apply q.injective
      exact Subtype.ext hjk⟩
  refine ⟨F.card, hFle, eF, ?_⟩
  ext x
  constructor
  · intro hx i
    by_cases hAi : A i = 0
    · have hz : 0 ≤ B i := by simpa [hAi] using hzero i
      change ⟪A i, x⟫ ≤ B i
      rw [hAi, inner_zero_left]
      exact hz
    · have hiF : i ∈ F := by simp [F, hAi]
      let z : {i : Fin n // i ∈ F} := ⟨i, hiF⟩
      obtain ⟨j, hj⟩ := q.surjective z
      have hval : eF j = i := by
        change (q j).1 = i
        exact congrArg Subtype.val hj
      have hxj := hx j
      simpa [A, B, hval] using hxj
  · intro hx j
    have hxj := hx (q j).1
    simpa [A, B, eF] using hxj


end HirschRowExcessPublic


theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (hdn : d ≤ n) :
    HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v
      (HirschCommonFace.commonFaceDim a b u v + (n - d)) := by
  exact HirschRowExcessPublic.common_face_has_subpresentation_faceDim_add_row_excess
    a b u v hu hdn

#print axioms solution
