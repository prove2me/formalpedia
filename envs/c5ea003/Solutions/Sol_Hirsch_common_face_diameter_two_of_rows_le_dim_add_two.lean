-- Prove2me | solution 1 for Hirsch.common_face_diameter_two_of_rows_le_dim_add_two
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T17:38:12.225217+00:00
-- url     : https://prove2.me/submissions/b9d5af5b-51d3-48dd-b008-a365a18b053e

import Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_rows_le_dim_add_three
import Theorems.Thm_Hirsch_common_face_diamLE_of_coord_diamLE

open scoped RealInnerProductSpace InnerProduct
open Set Module Hirsch
set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwoPublic

/-- Exact type of the already-Proved small-excess H-polyhedron theorem. -/
def SmallExcessBound : Prop :=
  ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    n ≤ d + 3 → Bornology.IsBounded (Hpoly a b) →
    DiamLE (Hpoly a b) (n - d)

/-- Exact type of the already-Proved common-face coordinate transport theorem. -/
def CommonFaceTransport : Prop :=
  ∀ {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)),
    DiamLE
      (Hpoly (HirschCommonFace.commonFaceA a b u x)
        (HirschCommonFace.commonFaceB a b u x)) B →
    DiamLE (HirschCommonFace.commonFace a b u x) B

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

/-- Under ambient row excess at most two, the canonical common-face coordinate
H-polyhedron has an equivalent subpresentation with at most `h+2` rows. -/
theorem common_face_has_subpresentation_dim_add_two_of_rows_le_dim_add_two
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (hrows : n ≤ d + 2) :
    HirschCommonFace.HasSubpresentationAtMost
      (HirschCommonFace.commonFaceA a b u v)
      (HirschCommonFace.commonFaceB a b u v)
      (HirschCommonFace.commonFaceDim a b u v + 2) := by
  classical
  let A := HirschCommonFace.commonFaceA a b u v
  let B := HirschCommonFace.commonFaceB a b u v
  let C := HirschCommonFace.commonSourceRows a b u v
  let F : Finset (Fin n) := Finset.univ.filter (fun i => A i ≠ 0)
  have hzero : (0 : EuclideanSpace ℝ (Fin (HirschCommonFace.commonFaceDim a b u v))) ∈
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
      Module.finrank ℝ T.range ≤ Module.finrank ℝ (C → ℝ) := Submodule.finrank_le _
      _ = C.card := by simp [Fintype.card_coe]
  have htotal : C.card + F.card ≤ n := by
    have hcard : (C ∪ F).card = C.card + F.card :=
      Finset.card_union_of_disjoint hdis
    have hle := Finset.card_le_card (Finset.subset_univ (C ∪ F))
    rw [hcard] at hle
    simpa using hle
  have hFle : F.card ≤ HirschCommonFace.commonFaceDim a b u v + 2 := by
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
    · have hz : 0 ≤ B i := by
        simpa [hAi] using hzero i
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

private theorem commonFace_coord_bounded {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    Bornology.IsBounded
      (Hpoly (HirschCommonFace.commonFaceA a b u v)
        (HirschCommonFace.commonFaceB a b u v)) := by
  obtain ⟨C, hC⟩ := hbd.exists_norm_le
  refine (isBounded_iff_forall_norm_le).2
    ⟨max 0 (C + ‖u‖), fun q hq => ?_⟩
  have hp : u + HirschCommonFace.commonFaceLift a b u v q ∈ Hpoly a b := by
    intro i
    have hi := hq i
    rw [commonFace_inner_restricted] at hi
    change ⟪a i, HirschCommonFace.commonFaceLift a b u v q⟫ ≤
      b i - ⟪a i, u⟫ at hi
    rw [inner_add_right]
    linarith
  have hCp := hC _ hp
  have hlift : ‖HirschCommonFace.commonFaceLift a b u v q‖ = ‖q‖ :=
    (HirschCommonFace.commonFaceLift a b u v).norm_map q
  have htri : ‖HirschCommonFace.commonFaceLift a b u v q‖ ≤
      ‖u + HirschCommonFace.commonFaceLift a b u v q‖ + ‖u‖ := by
    have h := norm_sub_le (u + HirschCommonFace.commonFaceLift a b u v q) u
    simpa using h
  have hmain : ‖q‖ ≤ C + ‖u‖ := by
    rw [← hlift]
    linarith
  exact hmain.trans (le_max_right _ _)

private lemma pad_walk {E : Type*} (R : E → E → Prop)
    {u v : E} {A B : ℕ} (hAB : A ≤ B)
    (w : ℕ → E) (h0 : w 0 = u) (hA : w A = v)
    (hs : ∀ j < A, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    ∃ w' : ℕ → E, w' 0 = u ∧ w' B = v ∧
      ∀ j < B, w' j = w' (j + 1) ∨ R (w' j) (w' (j + 1)) := by
  let w' : ℕ → E := fun j => w (min j A)
  refine ⟨w', ?_, ?_, ?_⟩
  · simpa only [w', Nat.zero_min] using h0
  · simpa only [w', Nat.min_eq_right hAB] using hA
  · intro j hj
    by_cases hjA : j < A
    · have h0' : j ≤ A := by omega
      have h1 : j + 1 ≤ A := by omega
      simpa only [w', Nat.min_eq_left h0', Nat.min_eq_left h1] using hs j hjA
    · have h0' : A ≤ j := by omega
      have h1 : A ≤ j + 1 := by omega
      exact Or.inl (by simp only [w', Nat.min_eq_right h0', Nat.min_eq_right h1])

/-- Compact composition driver for the public excess-two common-carrier theorem. -/
theorem excess_two_common_carrier_from_proved_inputs
    (hsmall : SmallExcessBound) (htransport : CommonFaceTransport)
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Hpoly a b) (hrows : n ≤ d + 2) :
    DiamLE (HirschCommonFace.commonFace a b u v) 2 := by
  obtain ⟨m, hm, e, he⟩ :=
    common_face_has_subpresentation_dim_add_two_of_rows_le_dim_add_two a b u v hu hrows
  have hbdCoord := commonFace_coord_bounded a b u v hbd
  have hbdSub : Bornology.IsBounded
      (Hpoly
        (fun j => HirschCommonFace.commonFaceA a b u v (e j))
        (fun j => HirschCommonFace.commonFaceB a b u v (e j))) := by
    rw [he]
    exact hbdCoord
  have hDsub := hsmall (HirschCommonFace.commonFaceDim a b u v) m
    (fun j => HirschCommonFace.commonFaceA a b u v (e j))
    (fun j => HirschCommonFace.commonFaceB a b u v (e j)) (by omega) hbdSub
  have hcost : m - HirschCommonFace.commonFaceDim a b u v ≤ 2 := by omega
  have hDsub2 : DiamLE
      (Hpoly
        (fun j => HirschCommonFace.commonFaceA a b u v (e j))
        (fun j => HirschCommonFace.commonFaceB a b u v (e j))) 2 := by
    intro x hx y hy
    obtain ⟨w, hw0, hwB, hs⟩ := hDsub x hx y hy
    exact pad_walk _ hcost w hw0 hwB hs
  have hDcoord : DiamLE
      (Hpoly (HirschCommonFace.commonFaceA a b u v)
        (HirschCommonFace.commonFaceB a b u v)) 2 := by
    rw [← he]
    exact hDsub2
  exact htransport a b u v hDcoord


end HirschExcessTwoPublic


theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Hpoly a b) (hrows : n ≤ d + 2) :
    DiamLE (HirschCommonFace.commonFace a b u v) 2 := by
  exact HirschExcessTwoPublic.excess_two_common_carrier_from_proved_inputs
    Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three
    Hirsch.common_face_diamLE_of_coord_diamLE
    a b u v hbd hu hrows
