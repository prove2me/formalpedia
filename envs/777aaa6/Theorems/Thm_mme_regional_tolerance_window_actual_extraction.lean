-- Prove2me | Theorems.Thm_mme_regional_tolerance_window_actual_extraction
-- name    : mme_regional_tolerance_window_actual_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T21:25:07.472824+00:00
-- url     : https://prove2.me/theorems/60a4c3d1-6375-4856-b586-4508daf697b2
-- title:
--   Actual finite tensor extraction for a physical tolerance window
-- statement:
--   Given integer regional structural data, nonnegative child tolerance delta, positive parent tolerance epsilon satisfying the explicit size test, and a uniform explicit finite-loss log budget a >= 0 over admissible nearby exact profiles, there is an actual tensor restriction extracting ceil(exp(a)) copies of the entire child tolerance-band CW tensor from polynomially many copies of the common parent tolerance-band CW tensor. This theorem derives the tensor maps and unique cover; neither is an assumption.
-- source:
--   Finite physical tolerance-window extraction for the More Asymmetry proof.

import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_CW_three_canonical_support
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Algebra.BigOperators.Fin
import Theorems.Thm_mme_regional_tolerance_window_step_family
import Theorems.Thm_mme_integer_regional_certified_log_copy_bound
import Theorems.Thm_mme_integer_regional_entropy_copy_bound
import Theorems.Thm_mme_integer_regional_step_realization
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Theorems.Thm_mme_basis_projected_type_cover_restrict
import Theorems.Thm_mme_type_cover_uniform_copy_extraction
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_modern_CW_power_nonzero_coefficient_fine_support

open MME MME.TensorObj MME.DWZStep1Support MME.CompleteSplit
open PiTensorProduct TensorProduct BigOperators Module

universe u

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MME.ProfiledCW

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

private theorem fine_support {K : Type u} [Field K] {N : ℕ}
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

open BigOperators MME MME.ProfiledCW MME.TensorObj MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem mme_regional_tolerance_window_actual_extraction {K : Type u} [Field K] {ell M : ℕ} {P : Predicate M}
    (D : IntegerStep ell M P) (delta eps rate : ℝ)
    (hdelta : 0 ≤ delta) (heps : 0 < eps) (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤ (D.minimum : ℝ) * eps^2)
    (hbudget : ∀ mu : WindowProfile D, WindowAdmissible D mu →
      (∀ i, WindowClose D delta i (mu i)) → rate ≤ windowLogBudget D mu eps) :
    ∃ types : ℕ,
      types ≤ (Fintype.card (Position D.n) + 1) ^
        (3 * Fintype.card (Cell D.half D.R D.parent) * Fintype.card (CompleteWord ell)) ∧
      Restrict (bigAdd (fun _ : Fin ⌈Real.exp rate⌉₊ ↦ tensor K (childWindow D delta)))
        (bigAdd (fun _ : Fin types ↦ tensor K (parentWindow D (eps+2*delta)))) := by
  sorry
