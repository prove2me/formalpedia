-- Prove2me | solution 1 for mme_modern_CW_power_nonzero_coefficient_boundary_histograms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:18:22.657717+00:00
-- url     : https://prove2.me/submissions/853d780a-8e09-4694-a2ab-9522f7d6d0ec

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_complete_split_profile_projection
import Theorems.Thm_mme_modern_CW_full_word_boundary_histograms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev

open MME MME.TensorObj MME.DWZStep1Support MME.CompleteSplit
open PiTensorProduct TensorProduct BigOperators Module

universe u v

set_option autoImplicit false
set_option warningAsError true

private theorem interchange_tprod_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  change (PiTensorProduct.lift interchangeOuter (tprod K v))
      (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
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
            (tprod K (fun _ ↦ (1 : K))) w = 1
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

private theorem source_pointwise_support
    {K : Type u} [Field K] (q ell N : ℕ)
    (w : Fin 3 → Fin (N * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2)))
    (hcoeff :
      (Basis.piTensorProduct (fun i ↦
        kronPowModeWordBasis (CWObj K q) i
          ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm)
          (N * 2 ^ (ell - 1)))).repr
        ((CWObj K q).kronPow (N * 2 ^ (ell - 1))).t w ≠ 0) :
    ∀ t : Fin N, ∀ r : Fin (2 ^ (ell - 1)),
      (cwThreeCanonicalGrading K q).blockTensor
        (fun i ↦ cwSquareCoordGrade q
          (w i (finProdFinEquiv (t, r))).down) ≠ 0 := by
  classical
  let b := fun i ↦ (cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm
  have hproduct :
      (∏ r : Fin (N * 2 ^ (ell - 1)),
        (Basis.piTensorProduct b).repr (CWObj K q).t (fun i ↦ w i r)) ≠ 0 := by
    rw [← power_coefficient_product (CWObj K q) b]
    exact hcoeff
  have hbgrade (i : Fin 3) (a : ULift.{u} (Fin (q + 2))) :
      b i a ∈ (cwThreeCanonicalGrading K q).classOf i
        (cwSquareCoordGrade q a.down) := by
    dsimp only [b]
    rw [Basis.reindex_apply]
    change cwThreeCanonicalBasis K q i a.down ∈
      cwBasisGrade (cwThreeCanonicalBasis K q i) (cwSquareCoordGrade q)
        (cwSquareCoordGrade q a.down)
    exact Submodule.subset_span ⟨a.down, rfl, rfl⟩
  intro t r
  exact nonzero_coefficient_nonzero_block (CWObj K q)
    (cwThreeCanonicalGrading K q) b
    (fun _ a ↦ cwSquareCoordGrade q a.down)
    hbgrade (fun i ↦ w i (finProdFinEquiv (t, r)))
    ((Finset.prod_ne_zero_iff.mp hproduct) _ (Finset.mem_univ _))

theorem solution
    {K : Type u} [Field K] (q ell N : ℕ)
    (w : Fin 3 → Fin (N * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2)))
    (hcoeff :
      (Basis.piTensorProduct (fun i ↦
        kronPowModeWordBasis (CWObj K q) i
          ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm)
          (N * 2 ^ (ell - 1)))).repr
        ((CWObj K q).kronPow (N * 2 ^ (ell - 1))).t w ≠ 0)
    {Cell : Type v} [DecidableEq Cell]
    (cell : Fin N → Cell) (coarse : Cell → Fin 3 → ℕ)
    (hCoarse : ∀ i t,
      ∑ r : Fin (2 ^ (ell - 1)),
        (cwSquareCoordGrade q (w i (finProdFinEquiv (t, r))).down).val =
          coarse (cell t) i) :
    let word : Fin 3 → Fin N → CompleteWord ell :=
      fun i t r ↦ cwSquareCoordGrade q (w i (finProdFinEquiv (t, r))).down
    (∀ s : Cell, coarse s 2 = 0 → ∀ sigma : CompleteWord ell,
      Fintype.card {t : Fin N // cell t = s ∧ word 1 t = sigma} =
        Fintype.card {t : Fin N //
          cell t = s ∧ word 0 t = fun r ↦ Fin.rev (sigma r)}) ∧
    (∀ s : Cell, coarse s 0 = 0 → ∀ sigma : CompleteWord ell,
      Fintype.card {t : Fin N // cell t = s ∧ word 2 t = sigma} =
        Fintype.card {t : Fin N //
          cell t = s ∧ word 1 t = fun r ↦ Fin.rev (sigma r)}) ∧
    (∀ s : Cell, coarse s 1 = 0 → ∀ sigma : CompleteWord ell,
      Fintype.card {t : Fin N // cell t = s ∧ word 2 t = sigma} =
        Fintype.card {t : Fin N //
          cell t = s ∧ word 0 t = fun r ↦ Fin.rev (sigma r)}) := by
  exact mme_modern_CW_full_word_boundary_histograms q cell coarse
    (fun i t r ↦ cwSquareCoordGrade q (w i (finProdFinEquiv (t, r))).down)
    hCoarse (source_pointwise_support q ell N w hcoeff)

