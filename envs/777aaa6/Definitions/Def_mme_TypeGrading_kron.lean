-- Prove2me | Definitions.Def_mme_TypeGrading_kron
-- name    : mme_TypeGrading_kron
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T03:17:42.657298+00:00
-- url     : https://prove2.me/theorems/cd372775-ba76-4253-8f72-7dc6a81e6b00
-- title:
--   Kronecker products of finite internal tensor gradings
-- statement:
--   Let a tensor $X$ have a finite internal grading with $t_X$ classes in each mode, and let $Y$ have one with $t_Y$ classes. Their Kronecker product admits the product grading indexed by pairs of classes. In every mode, the class at $(a,b)$ is canonically linearly equivalent to the tensor product of the class $a$ of $X$ and the class $b$ of $Y$. For block addresses $\sigma_X$ and $\sigma_Y$, the corresponding product block is exactly the modewise image of the interchange of the two factor blocks:
--
--   $$
--   (X\otimes Y)_{(\sigma_X,\sigma_Y)} = \bigotimes_i \lambda_i\!\left(X_{\sigma_X}\boxtimes Y_{\sigma_Y}\right),
--   $$
--
--   where each $\lambda_i$ is the canonical equivalence from the tensor product of the two class spaces to the paired class space. Consequently, a nonzero product block forces both factor blocks to be nonzero.
--
--   This gives the reusable grading and block-projection interface needed to assemble cyclic Coppersmith--Winograd tensors from individually graded factors.
--
--   **Formalization Note** Pairs of finite grade indices are encoded by the standard equivalence $\operatorname{Fin}(t_X)\times\operatorname{Fin}(t_Y)\simeq\operatorname{Fin}(t_Xt_Y)$.
-- source:
--   Standard tensor-product direct-sum decomposition; used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 264 and 270--272, https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_mmobj_mul
import Mathlib.RingTheory.Flat.Basic

open MME TensorProduct DirectSum Module

universe u

namespace MME.TensorObj.TypeGrading

variable {K : Type u} [Field K] {d tx ty : ℕ}
variable {X Y : TensorObj K d}

theorem blockProj_apply_mem
    (G : X.TypeGrading tx) (i : Fin d) (a : Fin tx)
    (x : X.V i) (hx : x ∈ G.classOf i a) :
    G.blockProj i a x = ⟨x, hx⟩ := by
  exact (G.is_internal i).ofBijective_coeLinearMap_of_mem hx

theorem blockProj_apply_mem_ne
    (G : X.TypeGrading tx) (i : Fin d) (a b : Fin tx)
    (hab : a ≠ b) (x : X.V i) (hx : x ∈ G.classOf i b) :
    G.blockProj i a x = 0 := by
  exact (G.is_internal i).ofBijective_coeLinearMap_of_mem_ne hab.symm hx

noncomputable def collectedFinBasis
    (G : X.TypeGrading tx) (i : Fin d) :
    Basis (Σ a : Fin tx,
      Fin (Module.finrank K (G.classOf i a))) K (X.V i) :=
  (G.is_internal i).collectedBasis
    (fun a ↦ Module.finBasis K (G.classOf i a))

private instance gradingKronScalarTower (V : Type u)
    [AddCommGroup V] [Module K V] : IsScalarTower K K V :=
  IsScalarTower.of_algebraMap_smul (by simp)

noncomputable def kronBasis
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty) (i : Fin d) :
    Basis
      ((Σ a : Fin tx, Fin (Module.finrank K (GX.classOf i a))) ×
       (Σ b : Fin ty, Fin (Module.finrank K (GY.classOf i b))))
      K ((TensorObj.kron X Y).V i) :=
  Module.Basis.tensorProduct (collectedFinBasis GX i)
    (collectedFinBasis GY i)

def kronBasisGrade
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty) (i : Fin d)
    (q :
      ((Σ a : Fin tx, Fin (Module.finrank K (GX.classOf i a))) ×
       (Σ b : Fin ty, Fin (Module.finrank K (GY.classOf i b))))) :
    Fin (tx * ty) :=
  finProdFinEquiv (q.1.1, q.2.1)

/-- Product grading on a Kronecker product, indexed by pairs of grades. -/
noncomputable def kronGrading
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty) :
    (TensorObj.kron X Y).TypeGrading (tx * ty) where
  decomp i := cwBasisGrade (kronBasis GX GY i) (kronBasisGrade GX GY i)
  is_internal i :=
    cwBasisGrade_isInternal (kronBasis GX GY i) (kronBasisGrade GX GY i)

noncomputable def classKronEmbed
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (i : Fin d) (a : Fin tx) (b : Fin ty) :
    (GX.classOf i a ⊗[K] GY.classOf i b) →ₗ[K]
      (TensorObj.kron X Y).V i :=
  TensorProduct.map (GX.classOf i a).subtype (GY.classOf i b).subtype

theorem classKronEmbed_mem
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (i : Fin d) (a : Fin tx) (b : Fin ty)
    (z : GX.classOf i a ⊗[K] GY.classOf i b) :
    classKronEmbed GX GY i a b z ∈
      (kronGrading GX GY).classOf i (finProdFinEquiv (a, b)) := by
  let bc := Module.Basis.tensorProduct
    (Module.finBasis K (GX.classOf i a))
    (Module.finBasis K (GY.classOf i b))
  rw [← bc.sum_repr z]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro q _
  apply Submodule.smul_mem
  unfold kronGrading cwBasisGrade
  apply Submodule.subset_span
  refine ⟨
    (⟨a, q.1⟩, ⟨b, q.2⟩), ?_, ?_⟩
  · simp [kronBasisGrade]
  · rw [Module.Basis.tensorProduct_apply]
    unfold kronBasis
    have hk := Module.Basis.tensorProduct_apply
      (collectedFinBasis GX i) (collectedFinBasis GY i)
      ⟨a, q.1⟩ ⟨b, q.2⟩
    exact hk.trans (by
      change
        ((GX.is_internal i).collectedBasis
            (fun a ↦ Module.finBasis K (GX.classOf i a))) ⟨a, q.1⟩ ⊗ₜ[K]
          ((GY.is_internal i).collectedBasis
            (fun b ↦ Module.finBasis K (GY.classOf i b))) ⟨b, q.2⟩ = _
      rw [DirectSum.IsInternal.collectedBasis_coe,
        DirectSum.IsInternal.collectedBasis_coe]
      change
        ((Module.finBasis K (GX.classOf i a) q.1 : GX.classOf i a) : X.V i) ⊗ₜ[K]
          ((Module.finBasis K (GY.classOf i b) q.2 : GY.classOf i b) : Y.V i) =
        TensorProduct.map (GX.classOf i a).subtype
          (GY.classOf i b).subtype
          (Module.finBasis K (GX.classOf i a) q.1 ⊗ₜ[K]
            Module.finBasis K (GY.classOf i b) q.2)
      exact (TensorProduct.map_tmul
        (R := K) (R₂ := K)
        (GX.classOf i a).subtype (GY.classOf i b).subtype
        (Module.finBasis K (GX.classOf i a) q.1)
        (Module.finBasis K (GY.classOf i b) q.2)).symm)

theorem classKronEmbed_range_eq
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (i : Fin d) (a : Fin tx) (b : Fin ty) :
    LinearMap.range (classKronEmbed GX GY i a b) =
      (kronGrading GX GY).classOf i (finProdFinEquiv (a, b)) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact classKronEmbed_mem GX GY i a b z
  · unfold kronGrading cwBasisGrade
    apply Submodule.span_le.2
    rintro _ ⟨q, hq, rfl⟩
    simp only [Set.mem_setOf_eq] at hq
    have hp : (q.1.1, q.2.1) = (a, b) := by
      exact finProdFinEquiv.injective hq
    have ha : q.1.1 = a := congrArg Prod.fst hp
    have hb : q.2.1 = b := congrArg Prod.snd hp
    obtain ⟨qa, qb⟩ := q
    obtain ⟨a', ua⟩ := qa
    obtain ⟨b', ub⟩ := qb
    dsimp only at ha hb
    subst a'
    subst b'
    change ∃ z, classKronEmbed GX GY i a b z =
      kronBasis GX GY i (⟨a, ua⟩, ⟨b, ub⟩)
    refine ⟨
      Module.finBasis K (GX.classOf i a) ua ⊗ₜ[K]
        Module.finBasis K (GY.classOf i b) ub, ?_⟩
    unfold kronBasis
    have hk := Module.Basis.tensorProduct_apply
      (collectedFinBasis GX i) (collectedFinBasis GY i)
      ⟨a, ua⟩ ⟨b, ub⟩
    apply Eq.trans ?_ hk.symm
    unfold collectedFinBasis classKronEmbed
    refine (TensorProduct.map_tmul
      (R := K) (R₂ := K)
      (GX.classOf i a).subtype (GY.classOf i b).subtype
      (Module.finBasis K (GX.classOf i a) ua)
      (Module.finBasis K (GY.classOf i b) ub)).trans ?_
    simp only [DirectSum.IsInternal.collectedBasis_coe]
    rfl

noncomputable def classKronLift
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (i : Fin d) (a : Fin tx) (b : Fin ty) :
    (GX.classOf i a ⊗[K] GY.classOf i b) →ₗ[K]
      (kronGrading GX GY).classOf i (finProdFinEquiv (a, b)) :=
  LinearMap.codRestrict _ (classKronEmbed GX GY i a b)
    (classKronEmbed_mem GX GY i a b)

theorem classKronLift_bijective
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (i : Fin d) (a : Fin tx) (b : Fin ty) :
    Function.Bijective (classKronLift GX GY i a b) := by
  constructor
  · intro x y hxy
    apply TensorProduct.map_injective_of_flat_flat
      (GX.classOf i a).subtype (GY.classOf i b).subtype
      (GX.classOf i a).subtype_injective
      (GY.classOf i b).subtype_injective
    exact congrArg Subtype.val hxy
  · intro y
    have hy : (y : (TensorObj.kron X Y).V i) ∈
        LinearMap.range (classKronEmbed GX GY i a b) := by
      rw [classKronEmbed_range_eq GX GY i a b]
      exact y.property
    obtain ⟨z, hz⟩ := hy
    refine ⟨z, Subtype.ext ?_⟩
    exact hz

noncomputable def classKronEquiv
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (i : Fin d) (a : Fin tx) (b : Fin ty) :
    (GX.classOf i a ⊗[K] GY.classOf i b) ≃ₗ[K]
      (kronGrading GX GY).classOf i (finProdFinEquiv (a, b)) :=
  LinearEquiv.ofBijective (classKronLift GX GY i a b)
    (classKronLift_bijective GX GY i a b)

theorem kronBasis_apply
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty) (i : Fin d)
    (qa : Σ a : Fin tx, Fin (Module.finrank K (GX.classOf i a)))
    (qb : Σ b : Fin ty, Fin (Module.finrank K (GY.classOf i b))) :
    kronBasis GX GY i (qa, qb) =
      collectedFinBasis GX i qa ⊗ₜ[K] collectedFinBasis GY i qb := by
  unfold kronBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

theorem kronBasis_mem
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (i : Fin d)
    (q :
      ((Σ a : Fin tx, Fin (Module.finrank K (GX.classOf i a))) ×
       (Σ b : Fin ty, Fin (Module.finrank K (GY.classOf i b))))) :
    kronBasis GX GY i q ∈
      (kronGrading GX GY).classOf i
        (finProdFinEquiv (q.1.1, q.2.1)) := by
  obtain ⟨⟨a, ua⟩, ⟨b, ub⟩⟩ := q
  let z := Module.finBasis K (GX.classOf i a) ua ⊗ₜ[K]
    Module.finBasis K (GY.classOf i b) ub
  have hz := classKronEmbed_mem GX GY i a b z
  suffices classKronEmbed GX GY i a b z =
      kronBasis GX GY i (⟨a, ua⟩, ⟨b, ub⟩) by
    rw [← this]
    exact hz
  unfold z classKronEmbed
  apply Eq.trans (TensorProduct.map_tmul _ _ _ _)
  rw [kronBasis_apply]
  unfold collectedFinBasis
  rw [DirectSum.IsInternal.collectedBasis_coe,
    DirectSum.IsInternal.collectedBasis_coe]
  rfl

theorem kronGrading_blockProj_eq
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (i : Fin d) (a : Fin tx) (b : Fin ty) :
    (kronGrading GX GY).blockProj i (finProdFinEquiv (a, b)) =
      (classKronLift GX GY i a b).comp
        (TensorProduct.map (GX.blockProj i a) (GY.blockProj i b)) := by
  apply (kronBasis GX GY i).ext
  rintro ⟨⟨a', ua⟩, ⟨b', ub⟩⟩
  have hxmem : collectedFinBasis GX i ⟨a', ua⟩ ∈ GX.classOf i a' :=
    (GX.is_internal i).collectedBasis_mem
      (fun a ↦ Module.finBasis K (GX.classOf i a)) ⟨a', ua⟩
  have hymem : collectedFinBasis GY i ⟨b', ub⟩ ∈ GY.classOf i b' :=
    (GY.is_internal i).collectedBasis_mem
      (fun b ↦ Module.finBasis K (GY.classOf i b)) ⟨b', ub⟩
  rw [kronBasis_apply]
  by_cases ha : a' = a
  · subst a'
    by_cases hb : b' = b
    · subst b'
      change _ = classKronLift GX GY i a b
        (TensorProduct.map (GX.blockProj i a) (GY.blockProj i b)
          (collectedFinBasis GX i ⟨a, ua⟩ ⊗ₜ[K]
            collectedFinBasis GY i ⟨b, ub⟩))
      rw [TensorProduct.map_tmul]
      rw [blockProj_apply_mem GX i a _ hxmem,
        blockProj_apply_mem GY i b _ hymem]
      rw [blockProj_apply_mem (kronGrading GX GY) i
        (finProdFinEquiv (a, b)) _]
      apply Subtype.ext
      rfl
    · have hpair : finProdFinEquiv (a, b) ≠
          finProdFinEquiv (a, b') := by
        intro h
        exact hb (congrArg Prod.snd (finProdFinEquiv.injective h)).symm
      rw [blockProj_apply_mem_ne (kronGrading GX GY) i
        (finProdFinEquiv (a, b)) (finProdFinEquiv (a, b')) hpair _]
      · change 0 = classKronLift GX GY i a b
          (TensorProduct.map (GX.blockProj i a) (GY.blockProj i b)
            (collectedFinBasis GX i ⟨a, ua⟩ ⊗ₜ[K]
              collectedFinBasis GY i ⟨b', ub⟩))
        rw [TensorProduct.map_tmul]
        rw [blockProj_apply_mem GX i a _ hxmem,
          blockProj_apply_mem_ne GY i b b' (Ne.symm hb) _ hymem]
        simp
      · simpa only [kronBasis_apply] using
          kronBasis_mem GX GY i (⟨a, ua⟩, ⟨b', ub⟩)
  · have hpair : finProdFinEquiv (a, b) ≠
        finProdFinEquiv (a', b') := by
      intro h
      exact ha (congrArg Prod.fst (finProdFinEquiv.injective h)).symm
    rw [blockProj_apply_mem_ne (kronGrading GX GY) i
      (finProdFinEquiv (a, b)) (finProdFinEquiv (a', b')) hpair _]
    · change 0 = classKronLift GX GY i a b
        (TensorProduct.map (GX.blockProj i a) (GY.blockProj i b)
          (collectedFinBasis GX i ⟨a', ua⟩ ⊗ₜ[K]
            collectedFinBasis GY i ⟨b', ub⟩))
      rw [TensorProduct.map_tmul]
      rw [blockProj_apply_mem_ne GX i a a' (Ne.symm ha) _ hxmem]
      simp
    · simpa only [kronBasis_apply] using
        kronBasis_mem GX GY i (⟨a', ua⟩, ⟨b', ub⟩)

private theorem kronInterchange_tprod
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (PiTensorProduct.tprod K v) (PiTensorProduct.tprod K w) =
      PiTensorProduct.tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  show (interchange (PiTensorProduct.tprod K v))
      (PiTensorProduct.tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v))
      (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- Naturality of the mode-wise interchange map under two families of maps. -/
theorem kronMap_interchange
    {V₁ V₂ V₃ V₄ : Fin d → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i ↦ TensorProduct.map (f i) (g i))
        (interchange t₁ t₂) =
      interchange (PiTensorProduct.map f t₁)
        (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      induction t₂ using PiTensorProduct.induction_on with
      | smul_tprod c' v' =>
          simp only [map_smul, LinearMap.smul_apply]
          rw [kronInterchange_tprod, PiTensorProduct.map_tprod,
            PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
            kronInterchange_tprod]
          simp only [TensorProduct.map_tmul]
      | add x y ih₁ ih₂ =>
          simp only [map_add, LinearMap.add_apply, ih₁, ih₂]
  | add x y ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

/-- The block tensor of the product grading is the interchange of the two
factor block tensors, transported into the corresponding product class. -/
theorem kronGrading_blockTensor_eq
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (sx : Fin d → Fin tx) (sy : Fin d → Fin ty) :
    (kronGrading GX GY).blockTensor
        (fun i ↦ finProdFinEquiv (sx i, sy i)) =
      PiTensorProduct.map
        (fun i ↦ classKronLift GX GY i (sx i) (sy i))
        (interchange (GX.blockTensor sx) (GY.blockTensor sy)) := by
  unfold TensorObj.TypeGrading.blockTensor
  change
    PiTensorProduct.map
        (fun i ↦ (kronGrading GX GY).blockProj i
          (finProdFinEquiv (sx i, sy i)))
        (interchange X.t Y.t) = _
  rw [← kronMap_interchange]
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have hproj :
      (fun i ↦ (kronGrading GX GY).blockProj i
        (finProdFinEquiv (sx i, sy i))) =
      (fun i ↦ (classKronLift GX GY i (sx i) (sy i)).comp
        (TensorProduct.map (GX.blockProj i (sx i))
          (GY.blockProj i (sy i)))) := by
    funext i
    exact kronGrading_blockProj_eq GX GY i (sx i) (sy i)
  rw [hproj]
  rfl

/-- A nonzero block of the product grading can only come from a nonzero
block of the left factor. -/
theorem kronGrading_blockTensor_ne_zero_left
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (sx : Fin d → Fin tx) (sy : Fin d → Fin ty)
    (h : (kronGrading GX GY).blockTensor
      (fun i ↦ finProdFinEquiv (sx i, sy i)) ≠ 0) :
    GX.blockTensor sx ≠ 0 := by
  intro hx
  apply h
  rw [kronGrading_blockTensor_eq, hx]
  rw [map_zero]
  rfl

/-- A nonzero block of the product grading can only come from a nonzero
block of the right factor. -/
theorem kronGrading_blockTensor_ne_zero_right
    (GX : X.TypeGrading tx) (GY : Y.TypeGrading ty)
    (sx : Fin d → Fin tx) (sy : Fin d → Fin ty)
    (h : (kronGrading GX GY).blockTensor
      (fun i ↦ finProdFinEquiv (sx i, sy i)) ≠ 0) :
    GY.blockTensor sy ≠ 0 := by
  intro hy
  apply h
  rw [kronGrading_blockTensor_eq, hy]
  change PiTensorProduct.map _ ((interchange (GX.blockTensor sx)) 0) = 0
  rw [map_zero]
  rfl

end MME.TensorObj.TypeGrading


