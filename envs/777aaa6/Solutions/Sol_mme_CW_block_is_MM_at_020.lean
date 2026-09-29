-- Prove2me | solution 1 for mme_CW_block_is_MM_at_020
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T02:06:14.416822+00:00
-- url     : https://prove2.me/submissions/b52c532f-d661-4f23-a443-4a88bade7bde

import Theorems.Thm_mme_CW_block_is_MM_at_020
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_canonical_grading
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_omega

/-! # `Sol_mme_CW_block_is_MM_at_020` — closes `mme_CW_block_is_MM_at_020`.

For the canonical 3-grading on `CWObj K q`, the σ-block at σ = (0,2,0) extracts
the single rank-one term `e_O ⊗ e_T ⊗ e_O` from `T_q`, which after class-
isomorphism is `MMObj K 1 1 1`.

This is the σ_002 case with modes 1 and 2 swapped: mode 1 evaluates at index
`q+1` against class 2; mode 2 evaluates at index `0` against class 0.

Status: LOCAL ONLY. -/

set_option maxHeartbeats 1200000

open MME PiTensorProduct BigOperators

universe u

namespace MMECWBlockAt020Sol

variable {K : Type u} [Field K] {q : ℕ}

/-- The σ-target for the (0, 2, 0) case. -/
def σ_020 : Fin 3 → Fin 3 := fun i =>
  match i with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

/-- The Restrict witness: a per-mode linear map from the block to MMObj K 1 1 1. -/
noncomputable def toMM (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3,
      ((cwCanonicalGrading q (K := K)).blockSubtensor σ_020).V i →ₗ[K]
        (MMObj K 1 1 1).V i :=
  fun i =>
    match i with
    | ⟨0, _⟩ =>
      LinearMap.smulRight
        ((LinearMap.proj (⟨0, by omega⟩ : Fin (q+2)) :
            (Fin (q+2) → K) →ₗ[K] K).comp
          (Submodule.subtype (cwGradePiece K q 0)))
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ =>
      LinearMap.smulRight
        ((LinearMap.proj (⟨q+1, by omega⟩ : Fin (q+2)) :
            (Fin (q+2) → K) →ₗ[K] K).comp
          (Submodule.subtype (cwGradePiece K q 2)))
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ =>
      LinearMap.smulRight
        ((LinearMap.proj (⟨0, by omega⟩ : Fin (q+2)) :
            (Fin (q+2) → K) →ₗ[K] K).comp
          (Submodule.subtype (cwGradePiece K q 0)))
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)

/-! ## blockProj evaluation helpers (re-derived locally). -/

private lemma blockProj_eq_aux {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t) (i : Fin d) (α : Fin t) (x : T.V i) :
    G.blockProj i α x =
      DirectSum.component K (Fin t)
        (fun β => (G.classOf i β : Submodule K (T.V i))) α
        ((G.modeLequiv i).symm x) := rfl

private lemma modeLequiv_symm_apply_aux {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t) (i : Fin d) (x : T.V i) :
    (G.modeLequiv i).symm x =
      (LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun α => (G.classOf i α : Submodule K (T.V i)))
        (G.is_internal i)).symm x := rfl

private lemma subtype_blockProj_self {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t)
    (i : Fin d) (α : Fin t) (v : T.V i) (hv : v ∈ G.classOf i α) :
    (G.classOf i α).subtype (G.blockProj i α v) = v := by
  rw [blockProj_eq_aux, modeLequiv_symm_apply_aux]
  show ((((LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun β => (G.classOf i β : Submodule K (T.V i)))
        (G.is_internal i)).symm v) α : G.classOf i α) : T.V i) = v
  rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem (G.is_internal i) hv]

private lemma subtype_blockProj_ne {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t)
    (i : Fin d) {α α' : Fin t} (hαα' : α ≠ α') (v : T.V i) (hv : v ∈ G.classOf i α) :
    (G.classOf i α').subtype (G.blockProj i α' v) = 0 := by
  rw [blockProj_eq_aux, modeLequiv_symm_apply_aux]
  show ((((LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun β => (G.classOf i β : Submodule K (T.V i)))
        (G.is_internal i)).symm v) α' : G.classOf i α') : T.V i) = 0
  rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne (G.is_internal i) hαα' hv]
  rfl

private lemma cw_subtype_blockProj_self_0 (q : ℕ) (α : Fin 3)
    (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α).subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨0, by omega⟩ α v) = v :=
  subtype_blockProj_self (cwCanonicalGrading q) ⟨0, by omega⟩ α v hv

private lemma cw_subtype_blockProj_self_1 (q : ℕ) (α : Fin 3)
    (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α).subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨1, by omega⟩ α v) = v :=
  subtype_blockProj_self (cwCanonicalGrading q) ⟨1, by omega⟩ α v hv

private lemma cw_subtype_blockProj_self_2 (q : ℕ) (α : Fin 3)
    (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α).subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨2, by omega⟩ α v) = v :=
  subtype_blockProj_self (cwCanonicalGrading q) ⟨2, by omega⟩ α v hv

private lemma cw_subtype_blockProj_ne_0 (q : ℕ) {α α' : Fin 3}
    (hαα' : α ≠ α') (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α').subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨0, by omega⟩ α' v) = 0 :=
  subtype_blockProj_ne (cwCanonicalGrading q) ⟨0, by omega⟩ hαα' v hv

private lemma cw_subtype_blockProj_ne_1 (q : ℕ) {α α' : Fin 3}
    (hαα' : α ≠ α') (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α').subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨1, by omega⟩ α' v) = 0 :=
  subtype_blockProj_ne (cwCanonicalGrading q) ⟨1, by omega⟩ hαα' v hv

private lemma cw_subtype_blockProj_ne_2 (q : ℕ) {α α' : Fin 3}
    (hαα' : α ≠ α') (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α').subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨2, by omega⟩ α' v) = 0 :=
  subtype_blockProj_ne (cwCanonicalGrading q) ⟨2, by omega⟩ hαα' v hv

/-! ## Pointwise evaluation. -/

private lemma toMM0_apply (K : Type u) [Field K] (q : ℕ)
    (w : cwGradePiece K q 0) :
    toMM K q ⟨0, by omega⟩ w =
      ((cwGradePiece K q 0).subtype w ⟨0, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  show LinearMap.smulRight ((LinearMap.proj (⟨0, by omega⟩ : Fin (q+2)) :
        (Fin (q+2) → K) →ₗ[K] K).comp
        (Submodule.subtype (cwGradePiece K q 0)))
      (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) w = _
  rw [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]

private lemma toMM1_apply (K : Type u) [Field K] (q : ℕ)
    (w : cwGradePiece K q 2) :
    toMM K q ⟨1, by omega⟩ w =
      ((cwGradePiece K q 2).subtype w ⟨q+1, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  show LinearMap.smulRight ((LinearMap.proj (⟨q+1, by omega⟩ : Fin (q+2)) :
        (Fin (q+2) → K) →ₗ[K] K).comp
        (Submodule.subtype (cwGradePiece K q 2)))
      (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) w = _
  rw [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]

private lemma toMM2_apply (K : Type u) [Field K] (q : ℕ)
    (w : cwGradePiece K q 0) :
    toMM K q ⟨2, by omega⟩ w =
      ((cwGradePiece K q 0).subtype w ⟨0, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  show LinearMap.smulRight ((LinearMap.proj (⟨0, by omega⟩ : Fin (q+2)) :
        (Fin (q+2) → K) →ₗ[K] K).comp
        (Submodule.subtype (cwGradePiece K q 0)))
      (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) w = _
  rw [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- σ_020 0 = 0 (class 0), eval at index 0. -/
private lemma toMM_blockProj_at0 (K : Type u) [Field K] (q : ℕ)
    (a : Fin (q+2)) :
    (toMM K q ⟨0, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨0, by omega⟩ 0
        (Pi.single a (1 : K) : Fin (q+2) → K)) =
      ((Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  classical
  rw [toMM0_apply]
  by_cases ha : typeOfCW q a = 0
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q 0 := by
      have := single_mem_cwGradePiece (K := K) q a
      rw [ha] at this; exact this
    rw [cw_subtype_blockProj_self_0 q 0
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q (typeOfCW q a) :=
      single_mem_cwGradePiece (K := K) q a
    have hne : (typeOfCW q a) ≠ (0 : Fin 3) := ha
    rw [cw_subtype_blockProj_ne_0 q hne
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
    have ha0 : a.val ≠ 0 := by
      intro h; apply ha; simp [typeOfCW, h]
    have hpi : (Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ = 0 := by
      rw [Pi.single_apply]
      have hne0 : (⟨0, by omega⟩ : Fin (q+2)) ≠ a := by
        intro heq; apply ha0
        have := congrArg Fin.val heq.symm; simpa using this
      rw [if_neg hne0]
    rw [hpi]; simp

/-- σ_020 1 = 2 (class 2), eval at index q+1. -/
private lemma toMM_blockProj_at1 (K : Type u) [Field K] (q : ℕ)
    (a : Fin (q+2)) :
    (toMM K q ⟨1, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨1, by omega⟩ 2
        (Pi.single a (1 : K) : Fin (q+2) → K)) =
      ((Pi.single a (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  classical
  rw [toMM1_apply]
  by_cases ha : typeOfCW q a = 2
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q 2 := by
      have := single_mem_cwGradePiece (K := K) q a
      rw [ha] at this; exact this
    rw [cw_subtype_blockProj_self_1 q 2
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q (typeOfCW q a) :=
      single_mem_cwGradePiece (K := K) q a
    have hne : (typeOfCW q a) ≠ (2 : Fin 3) := ha
    rw [cw_subtype_blockProj_ne_1 q hne
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
    have haq1 : a.val ≠ q + 1 := by
      intro h; apply ha; simp [typeOfCW, h]
    have hpi : (Pi.single a (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩ = 0 := by
      rw [Pi.single_apply]
      have hneq1 : (⟨q+1, by omega⟩ : Fin (q+2)) ≠ a := by
        intro heq; apply haq1
        have := congrArg Fin.val heq.symm; simpa using this
      rw [if_neg hneq1]
    rw [hpi]; simp

/-- σ_020 2 = 0 (class 0), eval at index 0. -/
private lemma toMM_blockProj_at2 (K : Type u) [Field K] (q : ℕ)
    (a : Fin (q+2)) :
    (toMM K q ⟨2, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨2, by omega⟩ 0
        (Pi.single a (1 : K) : Fin (q+2) → K)) =
      ((Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  classical
  rw [toMM2_apply]
  by_cases ha : typeOfCW q a = 0
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q 0 := by
      have := single_mem_cwGradePiece (K := K) q a
      rw [ha] at this; exact this
    rw [cw_subtype_blockProj_self_2 q 0
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q (typeOfCW q a) :=
      single_mem_cwGradePiece (K := K) q a
    have hne : (typeOfCW q a) ≠ (0 : Fin 3) := ha
    rw [cw_subtype_blockProj_ne_2 q hne
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
    have ha0 : a.val ≠ 0 := by
      intro h; apply ha; simp [typeOfCW, h]
    have hpi : (Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ = 0 := by
      rw [Pi.single_apply]
      have hne0 : (⟨0, by omega⟩ : Fin (q+2)) ≠ a := by
        intro heq; apply ha0
        have := congrArg Fin.val heq.symm; simpa using this
      rw [if_neg hne0]
    rw [hpi]; simp

/-! ## The composite `gMap i := toMM i ∘ blockProj i (σ_020 i)`. -/

private noncomputable def gMap (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3, (CWObj K q).V i →ₗ[K] (MMObj K 1 1 1).V i :=
  fun i => (toMM K q i).comp ((cwCanonicalGrading q (K := K)).blockProj i (σ_020 i))

private lemma map_toMM_block_eq_map_g (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (toMM K q)
      ((cwCanonicalGrading q (K := K)).blockSubtensor σ_020).t =
    PiTensorProduct.map (gMap K q) (CWTensor K q) := by
  show PiTensorProduct.map (toMM K q)
      ((cwCanonicalGrading q (K := K)).blockTensor σ_020) =
    PiTensorProduct.map (gMap K q) (CWTensor K q)
  unfold TensorObj.TypeGrading.blockTensor
  show ((PiTensorProduct.map (toMM K q)) ∘ₗ
      (PiTensorProduct.map (fun i => (cwCanonicalGrading q (K := K)).blockProj i (σ_020 i))))
        (CWObj K q).t = _
  rw [← PiTensorProduct.map_comp]
  rfl

/-! ## Evaluation of `gMap` on a CW monomial. -/

private lemma gMap_CWMonom (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q+2)) :
    PiTensorProduct.map (gMap K q) (CWMonom K q a b c) =
      (((Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩) *
        ((Pi.single b (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩) *
        ((Pi.single c (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩)) •
      tprod K (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
  unfold CWMonom
  erw [PiTensorProduct.map_tprod]
  set c0 : K := (Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ with hc0
  set c1 : K := (Pi.single b (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩ with hc1
  set c2 : K := (Pi.single c (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ with hc2
  have hfun : (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single a 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single b 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single c 1 : Fin (q+2) → K))) =
      (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => c0 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    funext s
    match s with
    | ⟨0, _⟩ =>
      show gMap K q ⟨0, _⟩ (Pi.single a 1 : Fin (q+2) → K) = _
      unfold gMap
      simp only [LinearMap.coe_comp, Function.comp_apply]
      show (toMM K q ⟨0, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨0, by omega⟩ 0)
        (Pi.single a 1 : Fin (q+2) → K)) = _
      rw [toMM_blockProj_at0]
    | ⟨1, _⟩ =>
      show gMap K q ⟨1, _⟩ (Pi.single b 1 : Fin (q+2) → K) = _
      unfold gMap
      simp only [LinearMap.coe_comp, Function.comp_apply]
      show (toMM K q ⟨1, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨1, by omega⟩ 2)
        (Pi.single b 1 : Fin (q+2) → K)) = _
      rw [toMM_blockProj_at1]
    | ⟨2, _⟩ =>
      show gMap K q ⟨2, _⟩ (Pi.single c 1 : Fin (q+2) → K) = _
      unfold gMap
      simp only [LinearMap.coe_comp, Function.comp_apply]
      show (toMM K q ⟨2, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨2, by omega⟩ 0)
        (Pi.single c 1 : Fin (q+2) → K)) = _
      rw [toMM_blockProj_at2]
  show (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single a 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single b 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single c 1 : Fin (q+2) → K))) = _
  have h_lhs := congrArg (fun f => (PiTensorProduct.tprod K) f) hfun
  simp only at h_lhs
  rw [h_lhs]
  let f0 : ∀ s : Fin 3, (MMObj K 1 1 1).V s := fun s =>
    match s with
    | ⟨0, _⟩ => c0 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ => c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ => c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
  let f1 : ∀ s : Fin 3, (MMObj K 1 1 1).V s := fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ => c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ => c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
  let f2 : ∀ s : Fin 3, (MMObj K 1 1 1).V s := fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ => c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
  let f3 : ∀ s : Fin 3, (MMObj K 1 1 1).V s := fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
  have eq_f0 : f0 = Function.update f1 (⟨0, by omega⟩ : Fin 3)
        (c0 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    funext s; match s with
    | ⟨0, _⟩ => simp [f0, f1, Function.update]
    | ⟨1, _⟩ => simp [f0, f1, Function.update]
    | ⟨2, _⟩ => simp [f0, f1, Function.update]
  have eq_f1 : Function.update f1 (⟨0, by omega⟩ : Fin 3)
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) =
      Function.update f2 (⟨1, by omega⟩ : Fin 3)
        (c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    funext s; match s with
    | ⟨0, _⟩ => simp [f1, f2, Function.update]
    | ⟨1, _⟩ => simp [f1, f2, Function.update]
    | ⟨2, _⟩ => simp [f1, f2, Function.update]
  have eq_f2 : Function.update f2 (⟨1, by omega⟩ : Fin 3)
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) =
      Function.update f3 (⟨2, by omega⟩ : Fin 3)
        (c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    funext s; match s with
    | ⟨0, _⟩ => simp [f2, f3, Function.update]
    | ⟨1, _⟩ => simp [f2, f3, Function.update]
    | ⟨2, _⟩ => simp [f2, f3, Function.update]
  have eq_f3 : Function.update f3 (⟨2, by omega⟩ : Fin 3)
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) = f3 := by
    funext s; match s with
    | ⟨0, _⟩ => simp [f3, Function.update]
    | ⟨1, _⟩ => simp [f3, Function.update]
    | ⟨2, _⟩ => simp [f3, Function.update]
  calc (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => c0 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K))
      = (PiTensorProduct.tprod K) f0 := rfl
    _ = (PiTensorProduct.tprod K) (Function.update f1 (⟨0, by omega⟩ : Fin 3)
          (c0 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K))) := by rw [eq_f0]
    _ = c0 • (PiTensorProduct.tprod K)
          (Function.update f1 (⟨0, by omega⟩ : Fin 3)
            (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
        exact MultilinearMap.map_update_smul (PiTensorProduct.tprod K) f1
          (⟨0, by omega⟩ : Fin 3) c0
          (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    _ = c0 • (PiTensorProduct.tprod K)
          (Function.update f2 (⟨1, by omega⟩ : Fin 3)
            (c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K))) := by rw [eq_f1]
    _ = c0 • (c1 • (PiTensorProduct.tprod K)
          (Function.update f2 (⟨1, by omega⟩ : Fin 3)
            (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K))) := by
        congr 1
        exact MultilinearMap.map_update_smul (PiTensorProduct.tprod K) f2
          (⟨1, by omega⟩ : Fin 3) c1
          (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    _ = c0 • (c1 • (PiTensorProduct.tprod K)
          (Function.update f3 (⟨2, by omega⟩ : Fin 3)
            (c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)))) := by rw [eq_f2]
    _ = c0 • (c1 • (c2 • (PiTensorProduct.tprod K)
          (Function.update f3 (⟨2, by omega⟩ : Fin 3)
            (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)))) := by
        congr 1; congr 1
        exact MultilinearMap.map_update_smul (PiTensorProduct.tprod K) f3
          (⟨2, by omega⟩ : Fin 3) c2
          (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    _ = c0 • (c1 • (c2 • (PiTensorProduct.tprod K) f3)) := by rw [eq_f3]
    _ = (c0 * c1 * c2) • (PiTensorProduct.tprod K) f3 := by
        rw [smul_smul, smul_smul]
    _ = (c0 * c1 * c2) • (PiTensorProduct.tprod K) (fun s : Fin 3 =>
          match s with
          | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
          | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
          | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := rfl

/-! ## Vanishing for non-OTO monomials, evaluation for OTO. -/

private lemma gMap_CWMonom_OTO (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨0, by omega⟩ : Fin (q+2)) (⟨q+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))) =
      tprod K (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
  rw [gMap_CWMonom]
  simp [Pi.single_eq_same]

/-- Vanishing of OMM: mode 1 has e_M (class 1), boundary eval at q+1 is 0. -/
private lemma gMap_CWMonom_OMM (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨0, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))) = 0 := by
  rw [gMap_CWMonom]
  have hi : i.val < q := i.isLt
  have hne : (⟨q+1, by omega⟩ : Fin (q+2)) ≠ (⟨i.val+1, by omega⟩ : Fin (q+2)) := by
    intro heq
    have h := congrArg Fin.val heq
    simp at h
    omega
  have hb : (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩ = 0 :=
    Pi.single_eq_of_ne hne 1
  rw [hb]; simp

/-- Vanishing of MOM: mode 0 has e_M (class 1), eval at 0 is 0. -/
private lemma gMap_CWMonom_MOM (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))) = 0 := by
  rw [gMap_CWMonom]
  have ha : (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ = 0 := by
    rw [Pi.single_apply]
    have : (⟨0, by omega⟩ : Fin (q+2)) ≠ ⟨i.val+1, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
    simp [if_neg this]
  rw [ha]; simp

/-- Vanishing of MMO: mode 0 has e_M (class 1), eval at 0 is 0. -/
private lemma gMap_CWMonom_MMO (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))) = 0 := by
  rw [gMap_CWMonom]
  have ha : (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ = 0 := by
    rw [Pi.single_apply]
    have : (⟨0, by omega⟩ : Fin (q+2)) ≠ ⟨i.val+1, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
    simp [if_neg this]
  rw [ha]; simp

/-- Vanishing of OOT: mode 1 has e_O (class 0), eval at q+1 is 0. -/
private lemma gMap_CWMonom_OOT (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨0, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))
        (⟨q+1, by omega⟩ : Fin (q+2))) = 0 := by
  rw [gMap_CWMonom]
  have hb : (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩ = 0 := by
    rw [Pi.single_apply]
    have : (⟨q+1, by omega⟩ : Fin (q+2)) ≠ ⟨0, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
    simp [if_neg this]
  rw [hb]; simp

/-- Vanishing of TOO: mode 0 has e_T (class 2), eval at 0 is 0. -/
private lemma gMap_CWMonom_TOO (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨q+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))) = 0 := by
  rw [gMap_CWMonom]
  have ha : (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ = 0 := by
    rw [Pi.single_apply]
    have : (⟨0, by omega⟩ : Fin (q+2)) ≠ ⟨q+1, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
    simp [if_neg this]
  rw [ha]; simp

end MMECWBlockAt020Sol

open MMECWBlockAt020Sol

theorem solution {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K 1 1 1)
      ((cwCanonicalGrading q (K := K)).blockSubtensor
        (fun i : Fin 3 =>
          match i with
          | ⟨0, _⟩ => 0
          | ⟨1, _⟩ => 2
          | ⟨2, _⟩ => 0)) := by
  refine ⟨MMECWBlockAt020Sol.toMM K q, ?_⟩
  show PiTensorProduct.map (MMECWBlockAt020Sol.toMM K q)
      ((cwCanonicalGrading q (K := K)).blockSubtensor MMECWBlockAt020Sol.σ_020).t =
      MMTensor K 1 1 1
  rw [map_toMM_block_eq_map_g]
  set O : Fin (q+2) := ⟨0, by omega⟩ with hO
  set T : Fin (q+2) := ⟨q+1, by omega⟩ with hT
  show PiTensorProduct.map (gMap K q)
      ((∑ i : Fin q,
          (CWMonom K q O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O)) +
        CWMonom K q O O T + CWMonom K q O T O + CWMonom K q T O O) = MMTensor K 1 1 1
  unfold MMTensor
  set F := PiTensorProduct.map (gMap K q) with hF
  set innerSum : PiTensorProduct K (CWSpace K q) := ∑ i : Fin q,
        (CWMonom K q O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O) with hInnerSum
  set bOOT : PiTensorProduct K (CWSpace K q) := CWMonom K q O O T with hbOOT
  set bOTO : PiTensorProduct K (CWSpace K q) := CWMonom K q O T O with hbOTO
  set bTOO : PiTensorProduct K (CWSpace K q) := CWMonom K q T O O with hbTOO
  suffices h : F innerSum + F bOOT + F bOTO + F bTOO = MMTensor K 1 1 1 by
    have rewrt : F (innerSum + bOOT + bOTO + bTOO) =
        F innerSum + F bOOT + F bOTO + F bTOO := by
      have eq1 : F ((innerSum + bOOT + bOTO) + bTOO) = F (innerSum + bOOT + bOTO) + F bTOO :=
        LinearMap.map_add F _ _
      have eq2 : F ((innerSum + bOOT) + bOTO) = F (innerSum + bOOT) + F bOTO :=
        LinearMap.map_add F _ _
      have eq3 : F (innerSum + bOOT) = F innerSum + F bOOT :=
        LinearMap.map_add F _ _
      calc F (innerSum + bOOT + bOTO + bTOO)
          = F (innerSum + bOOT + bOTO) + F bTOO := eq1
        _ = (F (innerSum + bOOT) + F bOTO) + F bTOO := by rw [eq2]
        _ = ((F innerSum + F bOOT) + F bOTO) + F bTOO := by rw [eq3]
    rw [rewrt]
    exact h
  rw [show F innerSum = ∑ i : Fin q, F (CWMonom K q O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O) from by
      rw [hInnerSum]
      exact _root_.map_sum F _ Finset.univ]
  have hF_triple : ∀ i : Fin q,
      F (CWMonom K q O
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
          CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
          CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O) = 0 := by
    intro i
    set M : Fin (q+2) := ⟨(i : Fin q).val + 1, by omega⟩ with hM
    have hsum : F (CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O) =
        F (CWMonom K q O M M) + F (CWMonom K q M O M) + F (CWMonom K q M M O) := by
      have e1 : F ((CWMonom K q O M M + CWMonom K q M O M) + CWMonom K q M M O) =
          F (CWMonom K q O M M + CWMonom K q M O M) + F (CWMonom K q M M O) :=
        LinearMap.map_add F _ _
      have e2 : F (CWMonom K q O M M + CWMonom K q M O M) =
          F (CWMonom K q O M M) + F (CWMonom K q M O M) :=
        LinearMap.map_add F _ _
      calc F (CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O)
          = F (CWMonom K q O M M + CWMonom K q M O M) + F (CWMonom K q M M O) := e1
        _ = (F (CWMonom K q O M M) + F (CWMonom K q M O M)) + F (CWMonom K q M M O) := by rw [e2]
    rw [hsum]
    rw [hO, hM, hF]
    rw [gMap_CWMonom_OMM K q i, gMap_CWMonom_MOM K q i, gMap_CWMonom_MMO K q i]
    simp
  rw [show (∑ i : Fin q, F (CWMonom K q O
          (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
          (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
        CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
          (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
        CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
          (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O)) = 0 from by
      apply Finset.sum_eq_zero
      intros i _
      exact hF_triple i]
  rw [show F (CWMonom K q O O T) = 0 from by
      rw [show O = (⟨0, by omega⟩ : Fin (q+2)) from rfl]
      rw [show T = (⟨q+1, by omega⟩ : Fin (q+2)) from rfl]
      exact gMap_CWMonom_OOT K q]
  rw [show F (CWMonom K q T O O) = 0 from by
      rw [show O = (⟨0, by omega⟩ : Fin (q+2)) from rfl]
      rw [show T = (⟨q+1, by omega⟩ : Fin (q+2)) from rfl]
      exact gMap_CWMonom_TOO K q]
  rw [show F (CWMonom K q O T O) = (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) from by
      rw [show O = (⟨0, by omega⟩ : Fin (q+2)) from rfl]
      rw [show T = (⟨q+1, by omega⟩ : Fin (q+2)) from rfl]
      exact gMap_CWMonom_OTO K q]
  simp only [zero_add, add_zero]
  unfold MMTensor
  rw [Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_one]
  rfl
