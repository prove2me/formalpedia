-- Prove2me | solution 1 for mme_basis_projected_type_cover_restrict
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T14:45:54.81077+00:00
-- url     : https://prove2.me/submissions/d27d7263-cdbb-466c-94bb-39560a2e9494

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_tensor_rank
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME Module PiTensorProduct BigOperators
universe u
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

private noncomputable def collect {K : Type u} [Field K] (T : TensorObj K 3) :
    {k : ℕ} → (B : Fin k → TensorObj K 3) →
      (∀ j i, (B j).V i →ₗ[K] T.V i) → ∀ i, (TensorObj.bigAdd B).V i →ₗ[K] T.V i
  | 0, _, _ => fun _ ↦ 0
  | 1, _, f => f 0
  | k + 2, B, f => fun i ↦ (f 0 i).coprod
      (collect T (fun j : Fin (k + 1) ↦ B j.succ) (fun j ↦ f j.succ) i)

private theorem collect_tensor {K : Type u} [Field K] (T : TensorObj K 3)
    {k : ℕ} (B : Fin k → TensorObj K 3) (f : ∀ j i, (B j).V i →ₗ[K] T.V i) :
    PiTensorProduct.map (collect T B f) (TensorObj.bigAdd B).t =
      ∑ j, PiTensorProduct.map (f j) (B j).t := by
  induction k using Nat.twoStepInduction with
  | zero =>
    simp only [TensorObj.bigAdd, TensorObj.zeroObj, Fin.sum_univ_zero]
    exact map_zero _
  | one =>
    simp only [TensorObj.bigAdd, collect, Fin.sum_univ_one]
  | more k ih ih' =>
    let C := TensorObj.bigAdd (fun j : Fin (k + 1) ↦ B j.succ)
    let g := collect T (fun j : Fin (k + 1) ↦ B j.succ) (fun j ↦ f j.succ)
    change PiTensorProduct.map (fun i ↦ (f 0 i).coprod (g i))
      (PiTensorProduct.map (fun i ↦ LinearMap.inl K ((B 0).V i) (C.V i)) (B 0).t +
       PiTensorProduct.map (fun i ↦ LinearMap.inr K ((B 0).V i) (C.V i)) C.t) = _
    rw [map_add]
    have hl : PiTensorProduct.map (fun i ↦ (f 0 i).coprod (g i))
        (PiTensorProduct.map (fun i ↦ LinearMap.inl K ((B 0).V i) (C.V i)) (B 0).t) =
        PiTensorProduct.map (f 0) (B 0).t := by
      calc
        _ = PiTensorProduct.map (fun i ↦ ((f 0 i).coprod (g i)).comp
            (LinearMap.inl K ((B 0).V i) (C.V i))) (B 0).t :=
          (LinearMap.congr_fun (PiTensorProduct.map_comp
            (f := fun i ↦ LinearMap.inl K ((B 0).V i) (C.V i))
            (g := fun i ↦ (f 0 i).coprod (g i))) (B 0).t).symm
        _ = _ := by
          have hh : (fun i ↦ ((f 0 i).coprod (g i)).comp
              (LinearMap.inl K ((B 0).V i) (C.V i))) = f 0 :=
            funext (fun i ↦ LinearMap.coprod_inl (f 0 i) (g i))
          exact congrArg (fun m ↦ PiTensorProduct.map m (B 0).t) hh
    have hr : PiTensorProduct.map (fun i ↦ (f 0 i).coprod (g i))
        (PiTensorProduct.map (fun i ↦ LinearMap.inr K ((B 0).V i) (C.V i)) C.t) =
        PiTensorProduct.map g C.t := by
      simpa only [LinearMap.coprod_inr] using
        (LinearMap.congr_fun (PiTensorProduct.map_comp
          (f := fun i ↦ LinearMap.inr K ((B 0).V i) (C.V i))
          (g := fun i ↦ (f 0 i).coprod (g i))) C.t).symm
    rw [hl, hr, ih']
    exact (Fin.sum_univ_succ (fun j ↦ PiTensorProduct.map (f j) (B j).t)).symm

private theorem reject {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (keep : ∀ i, I i → Prop) (i : Fin 3) (x : I i) (hx : ¬ keep i x) :
    (T.basisAllAllowedGrading b keep).blockProj i 0 (b i x) = 0 := by
  classical
  apply TensorObj.TypeGrading.blockProj_apply_mem_ne
    (T.basisAllAllowedGrading b keep) i 0 1 (by decide)
  exact Submodule.subset_span ⟨x, by simp [hx], rfl⟩

/-- A finite disjoint cover of retained coefficient types reconstructs the
whole projected tensor, charging one independent source per type. -/
theorem solution {K : Type u} [Field K] (T : TensorObj K 3) {k : ℕ}
    {I : Fin 3 → Type u} [∀ i, Fintype (I i)]
    (b : ∀ i, Basis (I i) K (T.V i))
    (parent : ∀ i, I i → Prop) (keep : Fin k → ∀ i, I i → Prop)
    (hsub : ∀ j i x, keep j i x → parent i x)
    (hcover : ∀ (x : ∀ i, I i), (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, parent i (x i)) → ∃! j, ∀ i, keep j i (x i)) :
    TensorObj.Restrict (T.basisAllAllowedSubtensor b parent)
      (TensorObj.bigAdd (fun j ↦ T.basisAllAllowedSubtensor b (keep j))) := by
  classical
  let P := T.basisAllAllowedSubtensor b parent
  let G := T.basisAllAllowedGrading b parent
  let B := fun j ↦ T.basisAllAllowedSubtensor b (keep j)
  let H := fun j ↦ T.basisAllAllowedGrading b (keep j)
  let f : ∀ j i, (B j).V i →ₗ[K] P.V i :=
    fun j i ↦ (G.blockProj i 0).comp ((H j).classOf i 0).subtype
  let F : ∀ j i, T.V i →ₗ[K] P.V i :=
    fun j i ↦ (f j i).comp ((H j).blockProj i 0)
  have hF (j i x) : F j i (b i x) =
      if keep j i x then G.blockProj i 0 (b i x) else 0 := by
    change G.blockProj i 0 (((H j).classOf i 0).subtype
      ((H j).blockProj i 0 (b i x))) = _
    by_cases hx : keep j i x
    · have hm : b i x ∈ (H j).classOf i 0 :=
        Submodule.subset_span ⟨x, by simp [hx], rfl⟩
      rw [TensorObj.TypeGrading.blockProj_apply_mem _ i 0 _ hm, if_pos hx]
      rfl
    · rw [reject T b (keep j) i x hx, map_zero, map_zero, if_neg hx]
  have hterm (j) (x : ∀ i, I i) :
      PiTensorProduct.map (F j) ((Basis.piTensorProduct b) x) =
        if ∀ i, keep j i (x i) then
          PiTensorProduct.map (fun i ↦ G.blockProj i 0) ((Basis.piTensorProduct b) x)
        else 0 := by
    rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod]
    by_cases hk : ∀ i, keep j i (x i)
    · rw [if_pos hk, PiTensorProduct.map_tprod]
      congr 1
      funext i
      exact (hF j i (x i)).trans (if_pos (hk i))
    · rw [if_neg hk]
      obtain ⟨i, hi⟩ := not_forall.mp hk
      apply (PiTensorProduct.tprod K).map_coord_zero i
      rw [hF, if_neg hi]
  refine ⟨collect P B f, (collect_tensor P B f).trans ?_⟩
  have himage (j) : PiTensorProduct.map (f j) (B j).t =
      PiTensorProduct.map (F j) T.t :=
    (LinearMap.congr_fun (PiTensorProduct.map_comp
      (f := fun i ↦ (H j).blockProj i 0) (g := f j)) T.t).symm
  simp only [himage]
  change (∑ j, PiTensorProduct.map (F j) T.t) =
    PiTensorProduct.map (fun i ↦ G.blockProj i 0) T.t
  rw [← (Basis.piTensorProduct b).sum_repr T.t]
  simp only [map_sum, map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hc : (Basis.piTensorProduct b).repr T.t x = 0
  · simp only [hc, zero_smul, Finset.sum_const_zero]
  · by_cases hp : ∀ i, parent i (x i)
    · obtain ⟨j, hj, hu⟩ := hcover x hc hp
      rw [Finset.sum_eq_single j]
      · rw [hterm, if_pos hj]
      · intro j' _ hne
        rw [hterm, if_neg (fun hh ↦ hne (hu j' hh))]
        exact smul_zero ((Basis.piTensorProduct b).repr T.t x)
      · simp
    · have hk (j) : ¬ ∀ i, keep j i (x i) :=
        fun hh ↦ hp (fun i ↦ hsub j i (x i) (hh i))
      obtain ⟨i, hi⟩ := not_forall.mp hp
      have hz : PiTensorProduct.map (fun i ↦ G.blockProj i 0)
          ((Basis.piTensorProduct b) x) = 0 := by
        rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod]
        exact (PiTensorProduct.tprod K).map_coord_zero i (reject T b parent i (x i) hi)
      rw [hz]
      change (∑ j, (Basis.piTensorProduct b).repr T.t x •
        PiTensorProduct.map (F j) ((Basis.piTensorProduct b) x)) =
        (Basis.piTensorProduct b).repr T.t x • (0 : PiTensorProduct K P.V)
      rw [smul_zero]
      apply Finset.sum_eq_zero
      intro j _
      rw [hterm, if_neg (hk j)]
      exact smul_zero ((Basis.piTensorProduct b).repr T.t x)
