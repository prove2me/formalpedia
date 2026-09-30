-- Prove2me | solution 1 for Hirsch.common_face_diameter_of_subpresentation_excess_le_three
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T18:07:05.161453+00:00
-- url     : https://prove2.me/submissions/5747cb24-6297-4efe-bb48-c25a525a8702

import Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_rows_le_dim_add_three
import Theorems.Thm_Hirsch_common_face_diamLE_of_coord_diamLE

open scoped RealInnerProductSpace InnerProduct
open Set Module Hirsch
set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschSmallCarrierPublic

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

/-- Public composition driver: an explicit common-face subpresentation with
row excess `r ≤ 3` gives intrinsic carrier graph diameter at most `r`. -/
theorem common_face_diameter_of_subpresentation_excess_le_three_from_proved_inputs
    (hsmall : SmallExcessBound) (htransport : CommonFaceTransport)
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (r : ℕ) (hr : r ≤ 3)
    (hsub : HirschCommonFace.HasSubpresentationAtMost
      (HirschCommonFace.commonFaceA a b u v)
      (HirschCommonFace.commonFaceB a b u v)
      (HirschCommonFace.commonFaceDim a b u v + r)) :
    DiamLE (HirschCommonFace.commonFace a b u v) r := by
  obtain ⟨m, hm, e, he⟩ := hsub
  have hbdCoord := commonFace_coord_bounded a b u v hbd
  have hbdSub : Bornology.IsBounded
      (Hpoly
        (fun j => HirschCommonFace.commonFaceA a b u v (e j))
        (fun j => HirschCommonFace.commonFaceB a b u v (e j))) := by
    rw [he]
    exact hbdCoord
  have hrows : m ≤ HirschCommonFace.commonFaceDim a b u v + 3 := by omega
  have hDsub := hsmall (HirschCommonFace.commonFaceDim a b u v) m
    (fun j => HirschCommonFace.commonFaceA a b u v (e j))
    (fun j => HirschCommonFace.commonFaceB a b u v (e j)) hrows hbdSub
  have hcost : m - HirschCommonFace.commonFaceDim a b u v ≤ r := by omega
  have hDsubR : DiamLE
      (Hpoly
        (fun j => HirschCommonFace.commonFaceA a b u v (e j))
        (fun j => HirschCommonFace.commonFaceB a b u v (e j))) r := by
    intro x hx y hy
    obtain ⟨w, hw0, hwB, hs⟩ := hDsub x hx y hy
    exact pad_walk _ hcost w hw0 hwB hs
  have hDcoord : DiamLE
      (Hpoly (HirschCommonFace.commonFaceA a b u v)
        (HirschCommonFace.commonFaceB a b u v)) r := by
    rw [← he]
    exact hDsubR
  exact htransport a b u v hDcoord


end HirschSmallCarrierPublic


theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (r : ℕ) (hr : r ≤ 3)
    (hsub : HirschCommonFace.HasSubpresentationAtMost
      (HirschCommonFace.commonFaceA a b u v)
      (HirschCommonFace.commonFaceB a b u v)
      (HirschCommonFace.commonFaceDim a b u v + r)) :
    DiamLE (HirschCommonFace.commonFace a b u v) r := by
  exact HirschSmallCarrierPublic.common_face_diameter_of_subpresentation_excess_le_three_from_proved_inputs
    Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three
    Hirsch.common_face_diamLE_of_coord_diamLE
    a b u v hbd r hr hsub
