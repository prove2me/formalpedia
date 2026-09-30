-- Prove2me | solution 1 for Hirsch.common_face_diamLE_of_coord_diamLE
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T03:48:54.962313+00:00
-- url     : https://prove2.me/submissions/67ba8241-b0e0-48e4-a1c8-37f3667f3288

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped RealInnerProductSpace InnerProduct
open Set Hirsch

noncomputable section

variable {d n : ℕ}

open HirschCommonFace

theorem commonFace_isExtreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    IsExtreme ℝ (Hpoly a b) (commonFace a b u x) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro p hp q hq z hz hzopen
    refine ⟨hp, ?_⟩
    intro i hiC
    have hztight : ⟪a i, z⟫ = b i := hz.2 i hiC
    have hp_le := hp i
    have hq_le := hq i
    obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzopen
    have hinner : ⟪a i, z⟫ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
      rw [← hzcomb]
      simp [inner_add_right, inner_smul_right]
    have hαpos : 0 < α := hα
    have hβnonneg : 0 ≤ β := hβ.le
    by_contra hptight
    have hp_lt : ⟪a i, p⟫ < b i := lt_of_le_of_ne hp_le hptight
    have h1 : α * ⟪a i, p⟫ < α * b i :=
      mul_lt_mul_of_pos_left hp_lt hαpos
    have h2 : β * ⟪a i, q⟫ ≤ β * b i :=
      mul_le_mul_of_nonneg_left hq_le hβnonneg
    have hb : α * b i + β * b i = b i := by
      rw [← add_mul, hαβ, one_mul]
    linarith

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

theorem commonFacePoint_injective
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    Function.Injective (commonFacePoint a b u x) := by
  intro p q hpq
  apply (commonFaceLift a b u x).injective
  have := congrArg (fun z => z - u) hpq
  simpa [commonFacePoint] using this

theorem commonFacePoint_surjOn
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    Set.SurjOn (commonFacePoint a b u x)
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x))
      (commonFace a b u x) := by
  intro y hy
  have hdir : y - u ∈ commonDirection a b u x :=
    (mem_commonFace_iff_sub_mem_commonDirection a b u x y).1 hy |>.2
  let wy : commonDirection a b u x := ⟨y - u, hdir⟩
  let q := commonFaceRepr a b u x wy
  have hpoint : commonFacePoint a b u x q = y := by
    change u + (((commonFaceRepr a b u x).symm
      ((commonFaceRepr a b u x) wy) : commonDirection a b u x) :
      EuclideanSpace ℝ (Fin d)) = y
    rw [(commonFaceRepr a b u x).symm_apply_apply]
    change u + (y - u) = y
    abel
  have hq : q ∈ Hpoly (commonFaceA a b u x) (commonFaceB a b u x) :=
    (mem_commonFace_coord_iff a b u x q).2 (hpoint ▸ hy)
  exact ⟨q, hq, hpoint⟩

theorem commonFacePoint_exists_preimage
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x y : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ commonFace a b u x) :
    ∃ q ∈ Hpoly (commonFaceA a b u x) (commonFaceB a b u x),
      commonFacePoint a b u x q = y :=
  (Set.mem_image (commonFacePoint a b u x)
    (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) y).1
    (commonFacePoint_surjOn a b u x hy)

theorem commonFacePoint_affine
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (α β : ℝ) (hαβ : α + β = 1)
    (p q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    commonFacePoint a b u x (α • p + β • q) =
      α • commonFacePoint a b u x p + β • commonFacePoint a b u x q := by
  simp only [commonFacePoint, map_add, map_smul, smul_add]
  rw [add_add_add_comm (α • u), ← add_smul, hαβ, one_smul]

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

theorem commonFace_coord_extreme_of_parent_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin (commonFaceDim a b u x)))
    (hz : z ∈ Hpoly (commonFaceA a b u x) (commonFaceB a b u x))
    (hparent : commonFacePoint a b u x z ∈ extremePoints ℝ (Hpoly a b)) :
    z ∈ extremePoints ℝ
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) := by
  refine ⟨hz, ?_⟩
  intro p hp q hq hseg
  have hpP : commonFacePoint a b u x p ∈ Hpoly a b :=
    ((mem_commonFace_coord_iff a b u x p).1 hp).1
  have hqP : commonFacePoint a b u x q ∈ Hpoly a b :=
    ((mem_commonFace_coord_iff a b u x q).1 hq).1
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hseg
  have hzSeg :
      commonFacePoint a b u x z ∈ openSegment ℝ
        (commonFacePoint a b u x p)
        (commonFacePoint a b u x q) := by
    refine ⟨α, β, hα, hβ, hαβ, ?_⟩
    calc
      α • commonFacePoint a b u x p +
          β • commonFacePoint a b u x q =
        commonFacePoint a b u x (α • p + β • q) :=
          (commonFacePoint_affine a b u x α β hαβ p q).symm
      _ = commonFacePoint a b u x z := by rw [hcomb]
  have hpZ : commonFacePoint a b u x p = commonFacePoint a b u x z :=
    hparent.2 hpP hqP hzSeg
  exact commonFacePoint_injective a b u x hpZ

theorem commonFacePoint_maps_adj'
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    {p q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))}
    (hadj : Adj (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) p q) :
    Adj (commonFace a b u x)
      (commonFacePoint a b u x p) (commonFacePoint a b u x q) := by
  have hne : commonFacePoint a b u x p ≠ commonFacePoint a b u x q :=
    fun h => hadj.1 (commonFacePoint_injective a b u x h)
  have hQp : p ∈ Hpoly (commonFaceA a b u x) (commonFaceB a b u x) :=
    hadj.2.1 (left_mem_segment _ p q)
  have hQq : q ∈ Hpoly (commonFaceA a b u x) (commonFaceB a b u x) :=
    hadj.2.1 (right_mem_segment _ p q)
  have hsubset :
      segment ℝ (commonFacePoint a b u x p) (commonFacePoint a b u x q) ⊆
        commonFace a b u x := by
    intro z hz
    obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hz
    have hlin : α • p + β • q ∈
        Hpoly (commonFaceA a b u x) (commonFaceB a b u x) := by
      intro i
      have hp := hQp i
      have hq := hQq i
      simp only [inner_add_right, inner_smul_right]
      have := add_le_add (mul_le_mul_of_nonneg_left hp hα)
        (mul_le_mul_of_nonneg_left hq hβ)
      have hsum : α * commonFaceB a b u x i + β * commonFaceB a b u x i =
          commonFaceB a b u x i := by
        calc
          α * commonFaceB a b u x i + β * commonFaceB a b u x i =
              (α + β) * commonFaceB a b u x i := by ring
          _ = commonFaceB a b u x i := by rw [hαβ, one_mul]
      linarith
    have hzφ : z = commonFacePoint a b u x (α • p + β • q) := by
      rw [← hcomb, commonFacePoint_affine a b u x α β hαβ p q]
    exact hzφ ▸ (mem_commonFace_coord_iff a b u x _).1 hlin
  refine ⟨hne, ⟨hsubset, ?_⟩⟩
  intro y hy z hz w hwseg hwopen
  let py := Classical.choose (commonFacePoint_exists_preimage a b u x y hy)
  have hpyφpair :=
    Classical.choose_spec (commonFacePoint_exists_preimage a b u x y hy)
  have hpy := hpyφpair.1
  have hpyφ := hpyφpair.2
  let pz := Classical.choose (commonFacePoint_exists_preimage a b u x z hz)
  have hpzφpair :=
    Classical.choose_spec (commonFacePoint_exists_preimage a b u x z hz)
  have hpz := hpzφpair.1
  have hpzφ := hpzφpair.2
  obtain ⟨α, β, hα, hβ, hαβ, hwyz⟩ := hwopen
  have hwφyz : w = commonFacePoint a b u x (α • py + β • pz) := by
    rw [← hwyz, ← hpyφ, ← hpzφ, commonFacePoint_affine a b u x α β hαβ py pz]
  obtain ⟨γ, δ, hγ, hδ, hγδ, hwpq⟩ := hwseg
  have hwφpq : w = commonFacePoint a b u x (γ • p + δ • q) := by
    rw [← hwpq, commonFacePoint_affine a b u x γ δ hγδ p q]
  have hpre : α • py + β • pz = γ • p + δ • q :=
    commonFacePoint_injective a b u x (hwφyz.symm.trans hwφpq)
  have hcoordSeg : α • py + β • pz ∈ segment ℝ p q := by
    refine ⟨γ, δ, hγ, hδ, hγδ, hpre.symm⟩
  have hcoordOpen : α • py + β • pz ∈ openSegment ℝ py pz :=
    ⟨α, β, hα, hβ, hαβ, rfl⟩
  have hpySeg : py ∈ segment ℝ p q :=
    hadj.2.left_mem_of_mem_openSegment hpy hpz hcoordSeg hcoordOpen
  obtain ⟨s, t, hs, ht, hst, hcomb⟩ := hpySeg
  refine ⟨s, t, hs, ht, hst, ?_⟩
  have haff := commonFacePoint_affine a b u x s t hst p q
  rw [← haff, hcomb]
  exact hpyφ

theorem solution
    {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hcoord : DiamLE
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) B) :
    DiamLE (commonFace a b u x) B := by
  intro p hp q hq
  have hpP : p ∈ extremePoints ℝ (Hpoly a b) :=
    (commonFace_isExtreme a b u x).extremePoints_subset_extremePoints hp
  have hqP : q ∈ extremePoints ℝ (Hpoly a b) :=
    (commonFace_isExtreme a b u x).extremePoints_subset_extremePoints hq
  let pp := Classical.choose (commonFacePoint_exists_preimage a b u x p hp.1)
  have hppφpair :=
    Classical.choose_spec (commonFacePoint_exists_preimage a b u x p hp.1)
  have hppQ := hppφpair.1
  have hpφ := hppφpair.2
  let qq := Classical.choose (commonFacePoint_exists_preimage a b u x q hq.1)
  have hqqφpair :=
    Classical.choose_spec (commonFacePoint_exists_preimage a b u x q hq.1)
  have hqqQ := hqqφpair.1
  have hqφ := hqqφpair.2
  have hppE : pp ∈ extremePoints ℝ
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) :=
    commonFace_coord_extreme_of_parent_extreme a b u x pp hppQ (by
      rw [hpφ]; exact hpP)
  have hqqE : qq ∈ extremePoints ℝ
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) :=
    commonFace_coord_extreme_of_parent_extreme a b u x qq hqqQ (by
      rw [hqφ]; exact hqP)
  obtain ⟨w, hw0, hwB, hstep⟩ := hcoord pp hppE qq hqqE
  refine ⟨fun j => commonFacePoint a b u x (w j), ?_, ?_, ?_⟩
  · change commonFacePoint a b u x (w 0) = p
    rw [hw0]
    exact hpφ
  · change commonFacePoint a b u x (w B) = q
    rw [hwB]
    exact hqφ
  · intro j hj
    cases hstep j hj with
    | inl hstay =>
      exact Or.inl (congrArg (commonFacePoint a b u x) hstay)
    | inr hadj =>
      exact Or.inr (commonFacePoint_maps_adj' a b u x hadj)

#print axioms solution
