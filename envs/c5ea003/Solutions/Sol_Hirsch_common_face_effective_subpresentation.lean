-- Prove2me | solution 1 for Hirsch.common_face_effective_subpresentation
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T03:24:24.159363+00:00
-- url     : https://prove2.me/submissions/3ad37bfd-daa1-49be-be49-1c00ca2eb8c2

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace InnerProduct
open Set Hirsch HirschCommonFace

variable {d n : ℕ}

/-- The origin of common-face coordinates is the first endpoint. If that
endpoint is feasible, the origin is feasible in the coordinate H-polytope,
so every zero restricted row is a tautology `0 ≤ B i`. -/
theorem commonFace_coord_zero_mem_of_u_mem
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) :
    (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) ∈
      Hpoly (commonFaceA a b u x) (commonFaceB a b u x) := by
  intro i
  -- ⟨commonFaceA i, 0⟩ = 0, so we need 0 ≤ commonFaceB i = b i - ⟨a i, u⟩
  have hi := hu i
  have hA0 : ⟪commonFaceA a b u x i, (0 : EuclideanSpace ℝ (Fin (commonFaceDim a b u x)))⟫ = 0 := by
    simp
  -- commonFaceB i = b i - ⟪a i, u⟫ from the definition
  -- Show 0 ≤ b i - ⟪a i, u⟫ from ⟨a i, u⟩ ≤ b i
  have : 0 ≤ commonFaceB a b u x i := by
    dsimp [commonFaceB]
    linarith [hi]
  simpa [hA0] using this

theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) :
    CommonFaceHasSubpresentationAtMost a b u x
      (commonFaceEffectiveCount a b u x) := by
  classical
  let A := commonFaceA a b u x
  let B := commonFaceB a b u x
  let F := commonFaceEffectiveRows a b u x
  let m := F.card
  have hm : m ≤ n := by
    simpa [m] using (Finset.card_le_univ F)
  -- Order-embedding of the effective index set into Fin n
  let e : Fin m ↪ Fin n :=
    ⟨fun j => (F.equivFin.symm j).1, by
      intro j k hjk
      have hval : (F.equivFin.symm j).1 = (F.equivFin.symm k).1 := hjk
      have : F.equivFin.symm j = F.equivFin.symm k := Subtype.ext hval
      exact F.equivFin.symm.injective this⟩
  refine ⟨m, le_rfl, e, ?_⟩
  ext q
  constructor
  · intro hq i
    by_cases hA : A i = 0
    · have h0 := commonFace_coord_zero_mem_of_u_mem a b u x hu
      have : 0 ≤ B i := by
        have hi := h0 i
        simpa [A, hA] using hi
      simpa [A, hA] using this
    · have hiF : i ∈ F := by
        dsimp [F, commonFaceEffectiveRows, A]
        exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hA⟩
      let z : {i : Fin n // i ∈ F} := ⟨i, hiF⟩
      let j := F.equivFin z
      have hj : e j = i := by
        change (F.equivFin.symm (F.equivFin z)).1 = i
        simp [z]
      have hqj := hq j
      simpa [A, B, hj] using hqj
  · intro hq j
    have hjF : (e j) ∈ F := by
      change (F.equivFin.symm j).1 ∈ F
      exact (F.equivFin.symm j).property
    exact hq (e j)

#print axioms solution
