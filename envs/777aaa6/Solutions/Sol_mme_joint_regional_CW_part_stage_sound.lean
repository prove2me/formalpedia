-- Prove2me | solution 1 for mme_joint_regional_CW_part_stage_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T00:55:20.959903+00:00
-- url     : https://prove2.me/submissions/925c58d4-9ab1-4b2b-bd40-a53884c90894

import Definitions.Def_mme_recursive_regional_CW_data
import Theorems.Thm_mme_recursive_regional_CW_plan_sound
import Theorems.Thm_mme_profiled_CW_region_product_restrict
import Theorems.Thm_mme_regional_copied_restrictions_product
import Theorems.Thm_mme_profiled_CW_mode_permutation_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Theorems.Thm_mme_basis_projected_type_cover_restrict
import Theorems.Thm_mme_type_cover_uniform_copy_extraction
import Theorems.Thm_mme_batched_restrictions_compose
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_CW_three_canonical_support
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_mme_joint_regional_CW_plan_data

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.DWZStep1Support MME.CompleteSplit Module PiTensorProduct TensorProduct
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

universe u

private theorem perm_sums' {K : Type u} [Field K] (sigma : Equiv.Perm (Fin 3))
    (T : TensorObj K 3) (n : ℕ) :
    Isomorphic (permObj sigma (bigAdd (fun _ : Fin n ↦ T)))
      (bigAdd (fun _ : Fin n ↦ permObj sigma T)) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [← TensorQ.permAut_toQ, TensorQ.toQ_bigAdd, map_sum, TensorQ.toQ_bigAdd]
  simp only [TensorQ.permAut_toQ]

/-- Mode permutation of a copy extraction between two profiled projections. -/
private theorem perm_copy_extraction {K : Type u} [Field K] {N : ℕ} (S T : Predicate N)
    (sigma : Equiv.Perm (Fin 3)) (hsigma : sigma = cyclicPerm ∨ sigma = swapFirstTwoPerm)
    (types copies : ℕ)
    (h : TensorObj.Restrict (bigAdd (fun _ : Fin copies ↦ tensor K T))
      (bigAdd (fun _ : Fin types ↦ tensor K S))) :
    TensorObj.Restrict (bigAdd (fun _ : Fin copies ↦ tensor K (fun i ↦ T (sigma.symm i))))
      (bigAdd (fun _ : Fin types ↦ tensor K (fun i ↦ S (sigma.symm i)))) := by
  exact (mme_bigAdd_mono_restrict (fun _ : Fin copies ↦
      (mme_profiled_CW_mode_permutation_iso T sigma hsigma).1)).trans
    ((perm_sums' sigma (tensor K T) copies).2.trans
      ((permObj_restrict sigma h).trans
        ((perm_sums' sigma (tensor K S) types).1.trans
          (mme_bigAdd_mono_restrict (fun _ : Fin types ↦
            (mme_profiled_CW_mode_permutation_iso S sigma hsigma).2)))))

private theorem interchange_tprod_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (PiTensorProduct.tprod K v) (PiTensorProduct.tprod K w) =
      PiTensorProduct.tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  change (PiTensorProduct.lift interchangeOuter (PiTensorProduct.tprod K v))
      (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem interchange_basis_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {ι κ : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (V i))
    (c : ∀ i, Basis (κ i) K (W i))
    (x : PiTensorProduct K V) (y : PiTensorProduct K W)
    (p : ∀ i, ι i) (q : ∀ i, κ i) :
    (Basis.piTensorProduct
        (fun i ↦ Module.Basis.tensorProduct (b i) (c i))).repr
        (interchange x y) (fun i ↦ (p i, q i)) =
      (Basis.piTensorProduct b).repr x p *
        (Basis.piTensorProduct c).repr y q := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod a' w =>
          simp [interchange_tprod_explicit, Finset.prod_mul_distrib]
          ring
      | add y z hy hz =>
          simp only [map_add, Finsupp.add_apply, mul_add, hy, hz]
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, Finsupp.add_apply,
        add_mul, hx, hz]

private theorem piTensorProduct_basis_reindex_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    {ι κ : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (V i))
    (e : ∀ i, ι i ≃ κ i) :
    Basis.piTensorProduct (fun i ↦ (b i).reindex (e i)) =
      (Basis.piTensorProduct b).reindex (Equiv.piCongrRight e) := by
  ext w
  simp [Basis.piTensorProduct_apply, Module.Basis.reindex_apply]

private noncomputable def powerBasis
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i)) (n : ℕ) :
    Basis (∀ i, Fin n → ι i) K
      (PiTensorProduct K (fun i ↦ (T.kronPow n).V i)) :=
  Basis.piTensorProduct (fun i ↦ kronPowModeWordBasis T i (b i) n)

private theorem power_coefficient_product
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (n : ℕ) (w : ∀ i, Fin n → ι i) :
    (powerBasis T b n).repr (T.kronPow n).t w =
      ∏ r : Fin n,
        (Basis.piTensorProduct b).repr T.t (fun i ↦ w i r) := by
  induction n with
  | zero =>
      change
        (Basis.piTensorProduct
          (fun i ↦ Basis.singleton (Fin 0 → ι i) K)).repr
            (PiTensorProduct.tprod K (fun _ ↦ (1 : K))) w = 1
      rw [Basis.piTensorProduct_repr_tprod_apply]
      simp only [Module.Basis.singleton_repr, Finset.prod_const_one]
  | succ n ih =>
      change
        (Basis.piTensorProduct
          (fun i ↦
            (Module.Basis.tensorProduct (b i)
              (kronPowModeWordBasis T i (b i) n)).reindex
                (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι i)))).repr
          (interchange T.t (T.kronPow n).t) w = _
      rw [piTensorProduct_basis_reindex_explicit]
      rw [Module.Basis.repr_reindex_apply]
      rw [interchange_basis_repr_explicit]
      simp only [Equiv.piCongrRight_symm_apply,
        Pi.map_apply, Fin.consEquiv_symm_apply]
      change
        (Basis.piTensorProduct b).repr T.t (fun i ↦ w i 0) *
          (powerBasis T b n).repr (T.kronPow n).t
            (fun i r ↦ w i r.succ) = _
      rw [ih, Fin.prod_univ_succ]

private theorem selected_coefficient_projection
    {K : Type u} [Field K] {d t : ℕ} (T : TensorObj K d)
    (G : T.TypeGrading t) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (grade : ∀ i, ι i → Fin t)
    (hgrade : ∀ i j, b i j ∈ G.classOf i (grade i j))
    (x : ∀ i, ι i) (i : Fin d) (v : T.V i) :
    (b i).repr
      ((G.classOf i (grade i (x i))).subtype
        (G.blockProj i (grade i (x i)) v)) (x i) =
      (b i).repr v (x i) := by
  classical
  have heq : ((b i).coord (x i)).comp
      (((G.classOf i (grade i (x i))).subtype).comp
        (G.blockProj i (grade i (x i)))) = (b i).coord (x i) := by
    apply (b i).ext
    intro j
    by_cases h : grade i j = grade i (x i)
    · have hm : b i j ∈ G.classOf i (grade i (x i)) := h ▸ hgrade i j
      simp only [LinearMap.comp_apply,
        TensorObj.TypeGrading.blockProj_apply_mem G i _ _ hm]
      rfl
    · have hne : j ≠ x i := fun hj ↦ h (congrArg (grade i) hj)
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        TensorObj.TypeGrading.blockProj_apply_mem_ne G i _ _ (Ne.symm h)
          _ (hgrade i j)]
      simp [Basis.coord_apply, hne]
  exact congrArg (fun f : T.V i →ₗ[K] K ↦ f v) heq

private theorem nonzero_coefficient_nonzero_block
    {K : Type u} [Field K] {d t : ℕ} (T : TensorObj K d)
    (G : T.TypeGrading t) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (grade : ∀ i, ι i → Fin t)
    (hgrade : ∀ i j, b i j ∈ G.classOf i (grade i j))
    (x : ∀ i, ι i)
    (hcoeff : (Basis.piTensorProduct b).repr T.t x ≠ 0) :
    G.blockTensor (fun i ↦ grade i (x i)) ≠ 0 := by
  intro hz
  let maps := fun i ↦ ((G.classOf i (grade i (x i))).subtype).comp
    (G.blockProj i (grade i (x i)))
  have hrepr (z : PiTensorProduct K T.V) :
      (Basis.piTensorProduct b).repr (PiTensorProduct.map maps z) x =
        (Basis.piTensorProduct b).repr z x := by
    induction z using PiTensorProduct.induction_on with
    | smul_tprod a v =>
        simp only [map_smul, PiTensorProduct.map_tprod,
          Finsupp.smul_apply, smul_eq_mul,
          Basis.piTensorProduct_repr_tprod_apply]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        exact selected_coefficient_projection T G b grade hgrade x i (v i)
    | add z z' hz hz' =>
        simp only [map_add, Finsupp.add_apply, hz, hz']
  have hmap : PiTensorProduct.map maps T.t = 0 := by
    change PiTensorProduct.map
      (fun i ↦ ((G.classOf i (grade i (x i))).subtype).comp
        (G.blockProj i (grade i (x i)))) T.t = 0
    rw [PiTensorProduct.map_comp]
    change PiTensorProduct.map
      (fun i ↦ (G.classOf i (grade i (x i))).subtype)
      (G.blockTensor (fun i ↦ grade i (x i))) = 0
    rw [hz, map_zero]
  apply hcoeff
  rw [← hrepr T.t, hmap, map_zero, Finsupp.zero_apply]

private theorem fine_support' {K : Type u} [Field K] {N : ℕ}
    (x : Fin 3 → Coordinate.{u} N)
    (hc : (Basis.piTensorProduct (canonical K N)).repr (raw K N).t x ≠ 0) :
    supported (fun i ↦ fine (x i)) := by
  classical
  let b := fun i ↦ (cwThreeCanonicalBasis K 5 i).reindex Equiv.ulift.symm
  have hproduct : (∏ r : Fin N,
      (Basis.piTensorProduct b).repr (CWObj K 5).t (fun i ↦ x i r)) ≠ 0 := by
    rw [← power_coefficient_product (CWObj K 5) b]
    exact hc
  have hbgrade (i : Fin 3) (a : ULift.{u} (Fin 7)) :
      b i a ∈ (cwThreeCanonicalGrading K 5).classOf i
        (cwSquareCoordGrade 5 a.down) := by
    dsimp only [b]
    rw [Basis.reindex_apply]
    exact Submodule.subset_span ⟨a.down, rfl, rfl⟩
  intro r
  have ht := nonzero_coefficient_nonzero_block (CWObj K 5)
    (cwThreeCanonicalGrading K 5) b (fun _ a ↦ cwSquareCoordGrade 5 a.down)
    hbgrade (fun i ↦ x i r)
    ((Finset.prod_ne_zero_iff.mp hproduct) r (Finset.mem_univ r))
  by_contra hn
  exact ht (mme_CW_three_canonical_support K 5 (fun i ↦ fine (x i) r) hn)




theorem solution {K : Type u} [Field K] {M lower : ℕ} {S T : Predicate M}
    (D : PartStage M lower S T) :
    TensorObj.Restrict (bigAdd (fun _ : Fin D.copies ↦ tensor K T))
      (bigAdd (fun _ : Fin D.types ↦ tensor K S)) := by
  induction D with
  | @step S T types copies steps enough inside cover =>
    have hcover : TensorObj.Restrict (tensor K T) (bigAdd (fun j ↦ tensor K (steps j).output)) := by
      apply mme_basis_projected_type_cover_restrict (raw K M) (canonical K M)
        (fun i x ↦ T i (fine x)) (fun j i x ↦ (steps j).output i (fine x))
        (fun j i x h ↦ inside j i (fine x) h)
      intro x hc hq
      exact cover (fun i ↦ fine (x i)) (fine_support' x hc) hq
    have hexact (j : Fin types) :
        TensorObj.Restrict (bigAdd (fun _ : Fin copies ↦ tensor K (steps j).output)) (tensor K S) :=
      (mme_bigAdd_prefix_restrict (by decide : 1 < 3) (enough j)
        (fun _ ↦ tensor K (steps j).output)).trans (mme_recursive_profiled_CW_exact_step (steps j))
    exact mme_type_cover_uniform_copy_extraction (tensor K S) (tensor K T)
      (fun j ↦ tensor K (steps j).output) hcover hexact
  | @rotate S T child ih =>
    exact perm_copy_extraction S T cyclicPerm (Or.inl rfl) child.types child.copies ih
  | @swap S T child ih =>
    exact perm_copy_extraction S T swapFirstTwoPerm (Or.inr rfl) child.types child.copies ih
