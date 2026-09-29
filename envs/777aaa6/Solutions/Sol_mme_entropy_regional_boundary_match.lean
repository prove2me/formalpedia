-- Prove2me | solution 1 for mme_entropy_regional_boundary_match
-- status  : ACCEPTED   (disprove)
-- author  : @Robertboy18
-- created : 2026-09-22T06:44:04.74504+00:00
-- url     : https://prove2.me/submissions/e34b6452-6698-41f6-94cc-66325ec7f942

import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.LinearAlgebra.PiTensorProduct
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Definitions.Def_mme_recursive_yz_cell_partition
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_mme_kronFin_mode_pi_basis
import Definitions.Def_mme_recursive_yz_boundary_data
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_tensor_bridge
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_mme_omega
import Definitions.Def_mme_tensor
import Definitions.Def_mme_flattening
import Definitions.Def_mme_entropy_regional_CW_recipe

set_option autoImplicit false

section
-- Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps

open MME PiTensorProduct BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

variable {K : Type u} [Field K]

private theorem scalarBundle0_map_sum_modes
    {k : ℕ} {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, Fin k → V i →ₗ[K] W i)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map (fun i ↦ ∑ j, f i j) x =
      ∑ js : Fin 3 → Fin k,
        PiTensorProduct.map (fun i ↦ f i (js i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      simp only [map_smul]
      simp only [PiTensorProduct.map_tprod, LinearMap.coe_sum,
        Finset.sum_apply]
      rw [MultilinearMap.map_sum (PiTensorProduct.tprod K) _]
      rw [Finset.smul_sum]
  | add x y ihx ihy =>
      simp only [map_add, ihx, ihy, Finset.sum_add_distrib]

private theorem scalarBundle0_bigAdd_t_eq_sum_slot :
    ∀ (k : ℕ) (B : Fin k → TensorObj K 3),
      (TensorObj.bigAdd B).t =
        ∑ j : Fin k,
          PiTensorProduct.map
            (fun i ↦ gradedBigAddSlot k B j i) (B j).t
  | 0, _ => by
      change (TensorObj.zeroObj : TensorObj K 3).t = ∑ j : Fin 0, _
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rfl
  | 1, B => by
      change (B 0).t =
        ∑ j : Fin 1,
          PiTensorProduct.map
            (fun i ↦ gradedBigAddSlot 1 B j i) (B j).t
      rw [Fin.sum_univ_one]
      change (B 0).t =
        PiTensorProduct.map (fun _ ↦ LinearMap.id) (B 0).t
      rw [PiTensorProduct.map_id]
      rfl
  | n + 2, B => by
      change PiTensorProduct.map (fun i ↦
              LinearMap.inl K ((B 0).V i)
                ((TensorObj.bigAdd (fun j ↦ B j.succ)).V i)) (B 0).t +
          PiTensorProduct.map (fun i ↦
              LinearMap.inr K ((B 0).V i)
                ((TensorObj.bigAdd (fun j ↦ B j.succ)).V i))
            (TensorObj.bigAdd (fun j ↦ B j.succ)).t =
        ∑ j : Fin (n + 2),
          PiTensorProduct.map
            (fun i ↦ gradedBigAddSlot (n + 2) B j i) (B j).t
      rw [Fin.sum_univ_succ]
      rw [scalarBundle0_bigAdd_t_eq_sum_slot (n + 1) (fun j ↦ B j.succ)]
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      rfl

theorem mme_tensor_family_direct_sum_restrict_of_mixed_maps
    (S : TensorObj K 3) {k : ℕ}
    (B : Fin k → TensorObj K 3)
    (f : ∀ j : Fin k, ∀ i : Fin 3, S.V i →ₗ[K] (B j).V i)
    (hDiagonal : ∀ j : Fin k,
      PiTensorProduct.map (f j) S.t = (B j).t)
    (hMixedZero : ∀ js : Fin 3 → Fin k,
      (∀ j : Fin k, js ≠ fun _ ↦ j) →
      PiTensorProduct.map (fun i ↦ f (js i) i) S.t = 0) :
    TensorObj.Restrict (TensorObj.bigAdd B) S := by
  classical
  let slotMap : ∀ i : Fin 3, Fin k →
      S.V i →ₗ[K] (TensorObj.bigAdd B).V i :=
    fun i j ↦ (gradedBigAddSlot k B j i).comp (f j i)
  refine ⟨fun i ↦ ∑ j, slotMap i j, ?_⟩
  rw [scalarBundle0_map_sum_modes slotMap S.t]
  rw [scalarBundle0_bigAdd_t_eq_sum_slot]
  let constChoice : Fin k → Fin 3 → Fin k := fun j _ ↦ j
  let diagonalChoices : Finset (Fin 3 → Fin k) :=
    Finset.univ.image constChoice
  have htermZero : ∀ js : Fin 3 → Fin k,
      js ∉ diagonalChoices →
      PiTensorProduct.map (fun i ↦ slotMap i (js i)) S.t = 0 := by
    intro js hjs
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    have hnonconstant : ∀ j : Fin k, js ≠ fun _ ↦ j := by
      intro j heq
      apply hjs
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, heq.symm⟩
    rw [hMixedZero js hnonconstant]
    exact LinearMap.map_zero _
  have hsplit :
      (∑ js : Fin 3 → Fin k,
          PiTensorProduct.map (fun i ↦ slotMap i (js i)) S.t) =
        ∑ js ∈ diagonalChoices,
          PiTensorProduct.map (fun i ↦ slotMap i (js i)) S.t := by
    symm
    apply Finset.sum_subset
    · exact Finset.subset_univ _
    · intro js _ hjs
      exact htermZero js hjs
  rw [hsplit]
  have hconstInjective : Function.Injective constChoice := by
    intro j₁ j₂ h
    exact congrFun h 0
  refine (Finset.sum_bij
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) ↦ constChoice j)
    (fun j _ ↦ Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    ?_ ?_ ?_).symm
  · intro j₁ _ j₂ _ h
    exact hconstInjective h
  · intro js hjs
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hjs
    exact ⟨j, Finset.mem_univ j, hj⟩
  · intro j _
    dsimp only [constChoice, slotMap]
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    rw [hDiagonal]

end

section
-- Theorems.Thm_mme_basis_projected_family_restrict

open MME Module PiTensorProduct BigOperators
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem scalarBundle1_rejected_projection
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) (keep : ∀ i, I i → Prop)
    (i : Fin 3) (x : I i) (hx : ¬ keep i x) :
    (T.basisAllAllowedGrading b keep).blockProj i 0 (b i x) = 0 := by
  classical
  apply TensorObj.TypeGrading.blockProj_apply_mem_ne
    (T.basisAllAllowedGrading b keep) i 0 1 (by decide)
  exact Submodule.subset_span ⟨x, by simp [hx], rfl⟩

private theorem scalarBundle1_nested_projection
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) (parent child : ∀ i, I i → Prop)
    (hsub : ∀ i x, child i x → parent i x) (i : Fin 3) :
    ((T.basisAllAllowedGrading b child).blockProj i 0).comp
      (((T.basisAllAllowedGrading b parent).classOf i 0).subtype.comp
        ((T.basisAllAllowedGrading b parent).blockProj i 0)) =
      (T.basisAllAllowedGrading b child).blockProj i 0 := by
  classical
  apply (b i).ext
  intro x
  simp only [LinearMap.comp_apply]
  by_cases hx : parent i x
  · have hm : b i x ∈ (T.basisAllAllowedGrading b parent).classOf i 0 :=
      Submodule.subset_span ⟨x, by simp [hx], rfl⟩
    rw [TensorObj.TypeGrading.blockProj_apply_mem _ i 0 _ hm]
    rfl
  · rw [scalarBundle1_rejected_projection T b parent i x hx, map_zero, map_zero,
      scalarBundle1_rejected_projection T b child i x (fun hc ↦ hx (hsub i x hc))]

/-- Coordinate support separation survives an existing parent projection. -/
theorem mme_basis_projected_family_restrict
    {K : Type u} [Field K] (T : TensorObj K 3) {k : ℕ}
    {I : Fin 3 → Type u} [∀ i, Fintype (I i)]
    (b : ∀ i, Basis (I i) K (T.V i))
    (parent : ∀ i, I i → Prop) (keep : Fin k → ∀ i, I i → Prop)
    (hsub : ∀ j i x, keep j i x → parent i x)
    (hunique : ∀ (x : ∀ i, I i) (js : Fin 3 → Fin k),
      (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, keep (js i) i (x i)) → ∃ j, js = fun _ ↦ j) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ T.basisAllAllowedSubtensor b (keep j)))
      (T.basisAllAllowedSubtensor b parent) := by
  classical
  let P := T.basisAllAllowedSubtensor b parent
  let G := T.basisAllAllowedGrading b parent
  let B := fun j ↦ T.basisAllAllowedSubtensor b (keep j)
  let f : ∀ j, ∀ i, T.V i →ₗ[K] (B j).V i :=
    fun j i ↦ (T.basisAllAllowedGrading b (keep j)).blockProj i 0
  let g : ∀ j, ∀ i, P.V i →ₗ[K] (B j).V i :=
    fun j i ↦ (f j i).comp (G.classOf i 0).subtype
  have hcomp (j i) : (g j i).comp (G.blockProj i 0) = f j i := by
    simpa only [g, LinearMap.comp_assoc] using scalarBundle1_nested_projection T b parent (keep j) (hsub j) i
  have hmap (js : Fin 3 → Fin k) :
      PiTensorProduct.map (fun i ↦ g (js i) i) P.t =
        PiTensorProduct.map (fun i ↦ f (js i) i) T.t := by
    change PiTensorProduct.map (fun i ↦ g (js i) i)
      (PiTensorProduct.map (fun i ↦ G.blockProj i 0) T.t) = _
    calc
      _ = PiTensorProduct.map (fun i ↦ (g (js i) i).comp (G.blockProj i 0)) T.t :=
        (LinearMap.congr_fun (PiTensorProduct.map_comp
          (f := fun i ↦ G.blockProj i 0) (g := fun i ↦ g (js i) i)) T.t).symm
      _ = _ := by simp only [hcomp]
  apply mme_tensor_family_direct_sum_restrict_of_mixed_maps P B g
  · intro j
    exact hmap (fun _ ↦ j)
  · intro js hnonconstant
    rw [hmap, ← (Basis.piTensorProduct b).sum_repr T.t, map_sum]
    apply Finset.sum_eq_zero
    intro x _
    rw [map_smul]
    by_cases hc : (Basis.piTensorProduct b).repr T.t x = 0
    · rw [hc, zero_smul]
    · have hr : ∃ i, ¬ keep (js i) i (x i) := by
        by_contra h
        have hk : ∀ i, keep (js i) i (x i) := fun i ↦ by
          by_contra hi
          exact h ⟨i, hi⟩
        obtain ⟨j, hj⟩ := hunique x js hc hk
        exact hnonconstant j hj
      obtain ⟨i, hi⟩ := hr
      have hz : f (js i) i (b i (x i)) = 0 :=
        scalarBundle1_rejected_projection T b (keep (js i)) i (x i) hi
      rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
        (PiTensorProduct.tprod K).map_coord_zero i hz, smul_zero]

end

section
-- Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis

open MME MME.TensorObj PiTensorProduct TensorProduct BigOperators Module

universe u

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

private theorem scalarBundle2_interchange_tprod_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  change (PiTensorProduct.lift interchangeOuter (PiTensorProduct.tprod K v))
      (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem scalarBundle2_interchange_basis_repr_explicit
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
          simp [scalarBundle2_interchange_tprod_explicit, Finset.prod_mul_distrib]
          ring
      | add y z hy hz =>
          simp only [map_add, Finsupp.add_apply, mul_add, hy, hz]
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, Finsupp.add_apply,
        add_mul, hx, hz]

private theorem scalarBundle2_piTensorProduct_basis_reindex_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    {ι κ : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (V i))
    (e : ∀ i, ι i ≃ κ i) :
    Basis.piTensorProduct (fun i ↦ (b i).reindex (e i)) =
      (Basis.piTensorProduct b).reindex (Equiv.piCongrRight e) := by
  ext w
  simp [Basis.piTensorProduct_apply,
    Module.Basis.reindex_apply]

private theorem scalarBundle2_basis_repr_equiv_explicit
    {K : Type u} [Field K]
    {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {ι κ : Type u} (B : Basis ι K V) (C : Basis κ K W) (E : ι ≃ κ)
    (x : V) (w : κ) :
    C.repr (B.equiv C E x) w = B.repr x (E.symm w) := by
  have h := congrArg (fun f : ι →₀ K ↦ f (E.symm w))
    ((C.reindex E.symm).repr.apply_symm_apply (B.repr x))
  change (C.reindex E.symm).repr
    ((C.reindex E.symm).repr.symm (B.repr x)) (E.symm w) = B.repr x (E.symm w) at h
  rw [Module.Basis.repr_reindex_apply] at h
  simpa [Module.Basis.equiv, LinearEquiv.trans_apply] using h

@[simp]
private theorem scalarBundle2_kronPowModeWordBasis_succ_apply_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) (i : Fin d) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ) (w : Fin (n + 1) → ι) :
    kronPowModeWordBasis T i b (n + 1) w =
      b (w 0) ⊗ₜ[K]
        kronPowModeWordBasis T i b n (fun r ↦ w r.succ) := by
  rw [kronPowModeWordBasis]
  calc
    _ = (Module.Basis.tensorProduct b
          (kronPowModeWordBasis T i b n))
        ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι)).symm w) :=
      Module.Basis.reindex_apply _ _ _
    _ = _ := by
      rw [Fin.consEquiv_symm_apply,
        Module.Basis.tensorProduct_apply]
      rfl

private noncomputable def scalarBundle2_kronPowTensorWordBasisExplicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i)) (n : ℕ) :
    Basis (∀ i, Fin n → ι i) K
      (PiTensorProduct K (fun i ↦ (T.kronPow n).V i)) :=
  Basis.piTensorProduct
    (fun i ↦ kronPowModeWordBasis T i (b i) n)

private theorem scalarBundle2_kronPowTensorWordBasis_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (n : ℕ) (w : ∀ i, Fin n → ι i) :
    (scalarBundle2_kronPowTensorWordBasisExplicit T b n).repr (T.kronPow n).t w =
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
      rw [scalarBundle2_piTensorProduct_basis_reindex_explicit]
      rw [Module.Basis.repr_reindex_apply]
      rw [scalarBundle2_interchange_basis_repr_explicit]
      simp only [Equiv.piCongrRight_symm_apply,
        Pi.map_apply, Fin.consEquiv_symm_apply]
      change
        (Basis.piTensorProduct b).repr T.t (fun i ↦ w i 0) *
          (scalarBundle2_kronPowTensorWordBasisExplicit T b n).repr (T.kronPow n).t
            (fun i r ↦ w i r.succ) = _
      rw [ih]
      rw [Fin.prod_univ_succ]

private theorem scalarBundle2_finite_product_coeff
    {K : Type u} [Field K] {d k : ℕ}
    (X : Fin k → TensorObj K d) {J : Fin k → Fin d → Type u}
    (b : ∀ j i, Basis (J j i) K ((X j).V i))
    (w : ∀ i j, J j i) :
    (Basis.piTensorProduct (fun i ↦ kronFinModePiBasis k X i (fun j ↦ b j i))).repr
      (kronFin k X).t w =
      ∏ j, (Basis.piTensorProduct (b j)).repr (X j).t (fun i ↦ w i j) := by
  induction k with
  | zero =>
      change (Basis.piTensorProduct
        (fun i ↦ Basis.singleton (∀ j : Fin 0, J j i) K)).repr
        (tprod K (fun _ ↦ (1 : K))) w = 1
      rw [Basis.piTensorProduct_repr_tprod_apply]
      simp only [Module.Basis.singleton_repr, Finset.prod_const_one]
  | succ k ih =>
      change (Basis.piTensorProduct (fun i ↦
        ((b 0 i).tensorProduct (kronFinModePiBasis k (fun j ↦ X j.succ) i
          (fun j ↦ b j.succ i))).reindex (Fin.consEquiv (fun j ↦ J j i)))).repr
        (interchange (X 0).t (kronFin k (fun j ↦ X j.succ)).t) w = _
      rw [scalarBundle2_piTensorProduct_basis_reindex_explicit, Module.Basis.repr_reindex_apply,
        scalarBundle2_interchange_basis_repr_explicit]
      simp only [Equiv.piCongrRight_symm_apply, Pi.map_apply, Fin.consEquiv_symm_apply]
      rw [ih, Fin.prod_univ_succ]
      rfl

private theorem scalarBundle2_map_basis_equiv_coeff
    {K : Type u} [Field K] {d : ℕ}
    (T S : TensorObj K d) {I J : Fin d → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) (c : ∀ i, Basis (J i) K (S.V i))
    (e : ∀ i, I i ≃ J i) (x : PiTensorProduct K T.V) (w : ∀ i, J i) :
    (Basis.piTensorProduct c).repr
      (PiTensorProduct.map (fun i ↦ (Basis.equiv (b i) (c i) (e i)).toLinearMap) x) w =
      (Basis.piTensorProduct b).repr x (fun i ↦ (e i).symm (w i)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
      simp only [map_smul, PiTensorProduct.map_tprod,
        Basis.piTensorProduct_repr_tprod_apply, Finsupp.smul_apply]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact scalarBundle2_basis_repr_equiv_explicit (b i) (c i) (e i) (v i) (w i)
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem mme_kronPow_fiber_grouping_preserves_tensor_and_basis {K : Type u} [Field K] {d N k : ℕ}
    (T : TensorObj K d) {I : Fin d → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) (count : Fin k → ℕ)
    (positions : Fin N ≃ (Σ j, Fin (count j))) :
    ∃ Φ : ∀ i, (T.kronPow N).V i ≃ₗ[K]
        (kronFin k (fun j ↦ T.kronPow (count j))).V i,
      PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap) (T.kronPow N).t =
        (kronFin k (fun j ↦ T.kronPow (count j))).t ∧
      ∀ i (w : Fin N → I i),
        Φ i (kronPowModeWordBasis T i (b i) N w) =
          kronFinModePiBasis k (fun j ↦ T.kronPow (count j)) i
            (fun j ↦ kronPowModeWordBasis T i (b i) (count j))
            (fun j r ↦ w (positions.symm ⟨j, r⟩)) := by
  let S := kronFin k (fun j ↦ T.kronPow (count j))
  let B := fun i ↦ kronPowModeWordBasis T i (b i) N
  let C := fun i ↦ kronFinModePiBasis k (fun j ↦ T.kronPow (count j)) i
    (fun j ↦ kronPowModeWordBasis T i (b i) (count j))
  let e : ∀ i, (Fin N → I i) ≃ (∀ j, Fin (count j) → I i) := fun i ↦ {
    toFun := fun w j r ↦ w (positions.symm ⟨j, r⟩)
    invFun := fun w r ↦ w (positions r).1 (positions r).2
    left_inv := by intro w; funext r; simp
    right_inv := by
      intro w; funext j r
      change (fun p : Σ j, Fin (count j) ↦ w p.1 p.2)
        (positions (positions.symm ⟨j, r⟩)) = _
      rw [positions.apply_symm_apply] }
  let Φ := fun i ↦ (B i).equiv (C i) (e i)
  refine ⟨Φ, ?_, ?_⟩
  · apply (Basis.piTensorProduct C).repr.injective
    ext w
    rw [scalarBundle2_map_basis_equiv_coeff (T.kronPow N) S B C e]
    change (scalarBundle2_kronPowTensorWordBasisExplicit T b N).repr (T.kronPow N).t
      (fun i r ↦ w i (positions r).1 (positions r).2) = _
    rw [scalarBundle2_kronPowTensorWordBasis_repr_explicit, scalarBundle2_finite_product_coeff]
    change _ = ∏ j, (scalarBundle2_kronPowTensorWordBasisExplicit T b (count j)).repr
      (T.kronPow (count j)).t (fun i ↦ w i j)
    simp_rw [scalarBundle2_kronPowTensorWordBasis_repr_explicit]
    calc
      _ = ∏ p : Σ j, Fin (count j),
          (Basis.piTensorProduct b).repr T.t (fun i ↦ w i p.1 p.2) :=
        Equiv.prod_comp positions _
      _ = _ := Fintype.prod_sigma _
  · intro i w
    exact Basis.equiv_apply _ _ _ _

end

section
-- Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes

open MME Module PiTensorProduct
open scoped Classical

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem scalarBundle3_projection_on_basis
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop) (i : Fin 3) (j : ι i) :
    let G := T.basisAllAllowedGrading b allowed
    (G.classOf i 0).subtype (G.blockProj i 0 (b i j)) =
      if allowed i j then b i j else 0 := by
  classical
  dsimp only
  let G := T.basisAllAllowedGrading b allowed
  by_cases hj : allowed i j
  · rw [if_pos hj]
    have hx : b i j ∈ G.classOf i 0 := by
      change b i j ∈ cwBasisGrade (b i)
        (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 0
      exact Submodule.subset_span
        ⟨j, by simp only [Set.mem_setOf_eq, if_pos hj], rfl⟩
    change (((G.modeLequiv i).symm (b i j)) 0 : T.V i) = b i j
    exact congrArg Subtype.val
      ((G.is_internal i).ofBijective_coeLinearMap_of_mem hx)
  · rw [if_neg hj]
    have hx : b i j ∈ G.classOf i 1 := by
      change b i j ∈ cwBasisGrade (b i)
        (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 1
      exact Submodule.subset_span
        ⟨j, by simp only [Set.mem_setOf_eq, if_neg hj], rfl⟩
    change (((G.modeLequiv i).symm (b i j)) 0 : T.V i) = 0
    exact congrArg Subtype.val
      ((G.is_internal i).ofBijective_coeLinearMap_of_mem_ne
        (show (1 : Fin 2) ≠ 0 by decide) hx)

/-- An actual extraction descends through the simultaneous all-mode
projection if each mode map kills every disallowed basis vector. -/
theorem mme_restrict_basisAllAllowedSubtensor_of_vanishes
    {K : Type u} [Field K] (T A : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop)
    (f : (i : Fin 3) → T.V i →ₗ[K] A.V i)
    (hmap : PiTensorProduct.map f T.t = A.t)
    (hvanish : ∀ i j, ¬ allowed i j → f i (b i j) = 0) :
    TensorObj.Restrict A (T.basisAllAllowedSubtensor b allowed) := by
  classical
  let G := T.basisAllAllowedGrading b allowed
  have hcomp : ∀ i,
      ((f i).comp (G.classOf i 0).subtype).comp (G.blockProj i 0) = f i := by
    intro i
    apply (b i).ext
    intro j
    change f i ((G.classOf i 0).subtype (G.blockProj i 0 (b i j))) = f i (b i j)
    rw [scalarBundle3_projection_on_basis]
    by_cases hj : allowed i j
    · rw [if_pos hj]
    · rw [if_neg hj, map_zero, hvanish i j hj]
  refine ⟨fun i ↦ (f i).comp (G.classOf i 0).subtype, ?_⟩
  change PiTensorProduct.map
      (fun i ↦ (f i).comp (G.classOf i 0).subtype)
      (PiTensorProduct.map (fun i ↦ G.blockProj i 0) T.t) = A.t
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  simpa only [hcomp] using hmap

end

section
-- Theorems.Thm_mme_recursive_yz_actual_cell_product_restriction

open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit Module PiTensorProduct
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
universe u v w

private theorem scalarBundle4_count_fiber {P : Type v} {C W : Type*} [Fintype P]
    {cell : P → C} (D : Partition cell) (f : P → W)
    (j : Fin D.parts) (a : W) :
    MME.RecursiveYZ.count cell f (D.cells j) a =
      MME.RecursiveYZ.count (fun _ : Fin (D.size j) ↦ Unit.unit)
        (fun r ↦ f (D.fiber j r).val) Unit.unit a := by
  classical
  unfold MME.RecursiveYZ.count
  simp only [true_and]
  symm
  apply Finset.card_bij (fun r _ ↦ (D.fiber j r).val)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact ⟨(D.fiber j r).property, hr⟩
  · intro r hr s hs heq
    exact (D.fiber j).injective (Subtype.ext heq)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    let x : {p : P // cell p = D.cells j} := ⟨p, hp.1⟩
    refine ⟨(D.fiber j).symm x, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply] using hp.2
    · exact congrArg Subtype.val ((D.fiber j).apply_symm_apply x)

private theorem scalarBundle4_label_fiber {P : Type v} {C : Type w} {cell : P → C}
    (D : Partition cell) (q ell L : ℕ) (e : Fin L ≃ P)
    (x : WordIndex.{u} q ell L) (j : Fin D.parts) (r : Fin (D.size j)) :
    label q ell (D.size j) (Equiv.refl _)
      (fun a ↦ x (D.leaves ell L e ⟨j,a⟩)) r =
    label q ell L e x (D.fiber j r).val := by
  funext s
  simp [label, Partition.leaves]

private theorem scalarBundle4_allowed_of_fibers {P : Type v} {C : Type w} [Fintype P]
    {cell : P → C} (D : Partition cell) (q ell L : ℕ) (e : Fin L ≃ P)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (i : Fin 3) (x : WordIndex.{u} q ell L)
    (h : ∀ j, allowed q ell (D.size j) (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ ↦ shape (D.cells j)) (fun a _ ↦ mu a (D.cells j)) i
      (fun a ↦ x (D.leaves ell L e ⟨j,a⟩))) :
    allowed q ell L e cell shape mu i x := by
  constructor
  · intro p
    obtain ⟨⟨j,r⟩, hp⟩ := D.positions.surjective p
    have hc : cell (D.fiber j r).val = D.cells j := (D.fiber j r).property
    have hg := (h j).1 r
    rw [scalarBundle4_label_fiber] at hg
    change D.positions ⟨j,r⟩ = p at hp
    rw [Partition.positions_apply] at hp
    simpa only [hp, ← hc] using hg
  · intro c a
    obtain ⟨j,rfl⟩ := D.cells.surjective c
    rw [scalarBundle4_count_fiber]
    have hh := (h j).2 Unit.unit a
    have hl : label q ell (D.size j) (Equiv.refl _)
        (fun a ↦ x (D.leaves ell L e ⟨j,a⟩)) =
        (fun r ↦ label q ell L e x (D.fiber j r).val) := by
      funext r; exact scalarBundle4_label_fiber D q ell L e x j r
    rw [hl] at hh
    exact hh

theorem mme_recursive_yz_actual_cell_product_restriction {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (D : Partition cell) :
    Restrict (kronFin D.parts (D.piece K q ell shape mu))
      (unbroken K q ell L positions cell shape mu) := by
  classical
  let raw := fun j : Fin D.parts ↦ source K q ell (D.size j)
  let child := D.piece K q ell shape mu
  let G := fun j : Fin D.parts ↦
    grading K q ell (D.size j) (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ ↦ shape (D.cells j)) (fun i _ ↦ mu i (D.cells j))
  let proj := fun j i ↦ (G j).blockProj i 0
  obtain ⟨Φ, ht, hb⟩ := mme_kronPow_fiber_grouping_preserves_tensor_and_basis
    (CWObj K q) (fun i ↦ (MME.DWZStep1Support.cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm)
    (fun j ↦ D.size j * 2 ^ (ell - 1)) (D.leaves ell L positions).symm
  change PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap) (source K q ell L).t =
    (kronFin D.parts raw).t at ht
  have hB (i : Fin 3) (x : WordIndex.{u} q ell L) :
      Φ i (basis K q ell L i x) =
        kronFinModePiBasis D.parts raw i (fun j ↦ basis K q ell (D.size j) i)
          (fun j a ↦ x (D.leaves ell L positions ⟨j,a⟩)) := hb i x
  let F := fun i ↦ (kronFinFamilyModeMap D.parts raw child proj i).comp (Φ i).toLinearMap
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes (source K q ell L)
    (kronFin D.parts child) (basis K q ell L)
    (allowed q ell L positions cell shape mu) F
  · change PiTensorProduct.map (fun i ↦
      (kronFinFamilyModeMap D.parts raw child proj i).comp (Φ i).toLinearMap)
        (source K q ell L).t = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    exact (congrArg (PiTensorProduct.map
      (kronFinFamilyModeMap D.parts raw child proj)) ht).trans
      (kronFinFamilyModeMap_preserves_tensor raw child proj (fun _ ↦ rfl))
  · intro i x hx
    change kronFinFamilyModeMap D.parts raw child proj i
      (Φ i (basis K q ell L i x)) = 0
    rw [hB]
    apply kronFinFamilyModeMap_basis_eq_zero_of_exists raw child i
      (fun j ↦ basis K q ell (D.size j) i) proj
    have hn : ¬ ∀ j, allowed q ell (D.size j) (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ shape (D.cells j)) (fun a _ ↦ mu a (D.cells j)) i
        (fun a ↦ x (D.leaves ell L positions ⟨j,a⟩)) :=
      fun h ↦ hx (scalarBundle4_allowed_of_fibers D q ell L positions shape mu i x h)
    obtain ⟨j,hj⟩ := not_forall.mp hn
    refine ⟨j, ?_⟩
    apply TensorObj.TypeGrading.blockProj_apply_mem_ne (G j) i 0 1 (by decide)
    change basis K q ell (D.size j) i _ ∈ Submodule.span K
      (basis K q ell (D.size j) i '' {w | (if allowed q ell (D.size j) (Equiv.refl _)
        (fun _ ↦ Unit.unit) (fun _ ↦ shape (D.cells j))
        (fun a _ ↦ mu a (D.cells j)) i w then (0 : Fin 2) else 1) = 1})
    exact Submodule.subset_span
      ⟨(fun a ↦ x (D.leaves ell L positions ⟨j,a⟩)), if_neg hj, rfl⟩

end

section
-- Theorems.Thm_mme_fintype_fixed_fiber_function_card

open Equiv MulAction

set_option autoImplicit false

/-- Functions on a finite domain with the same fiber sizes as a fixed
function are counted by the corresponding multinomial coefficient. -/
theorem mme_fintype_fixed_fiber_function_card
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (f : α → ι) :
    Fintype.card
        {g : α → ι // ∀ i,
          Fintype.card {a // g a = i} =
            Fintype.card {a // f a = i}} =
      (Fintype.card α).factorial /
        ∏ i, (Fintype.card {a // f a = i}).factorial := by
  classical
  let G := (Equiv.Perm α)ᵈᵐᵃ
  letI : Fintype G := Fintype.ofEquiv (Equiv.Perm α) DomMulAct.mk
  let P : (α → ι) → Prop := fun g => ∀ i,
    Fintype.card {a // g a = i} = Fintype.card {a // f a = i}
  have horbit : ∀ g : α → ι,
      g ∈ MulAction.orbit G f ↔ P g := by
    intro g
    constructor
    · rw [MulAction.mem_orbit_iff]
      rintro ⟨c, rfl⟩ i
      let e : {a // (c • f) a = i} ≃ {a // f a = i} :=
        Equiv.subtypeEquiv (DomMulAct.mk.symm c) (fun a => by
          change (f (DomMulAct.mk.symm c a) = i) ↔
            f (DomMulAct.mk.symm c a) = i
          rfl)
      exact Fintype.card_congr e
    · intro hg
      let e : ∀ i, {a // g a = i} ≃ {a // f a = i} :=
        fun i => Fintype.equivOfCardEq (hg i)
      let π : Equiv.Perm α := Equiv.ofFiberEquiv e
      rw [MulAction.mem_orbit_iff]
      refine ⟨DomMulAct.mk π, ?_⟩
      funext a
      change f (π a) = g a
      exact Equiv.ofFiberEquiv_map e a
  let orbitEquiv : MulAction.orbit G f ≃ {g : α → ι // P g} :=
    Equiv.subtypeEquiv (Equiv.refl (α → ι)) (fun g => by
      simpa only [Equiv.refl_apply] using horbit g)
  have horbitCard :
      Fintype.card {g : α → ι // P g} *
          Fintype.card (MulAction.stabilizer G f) =
        Fintype.card G := by
    rw [← Fintype.card_congr orbitEquiv]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G f
  have hstab :
      Fintype.card (MulAction.stabilizer G f) =
        ∏ i, (Fintype.card {a // f a = i}).factorial := by
    let e : MulAction.stabilizer G f ≃
        {g : Equiv.Perm α // f ∘ g = f} :=
      Equiv.subtypeEquiv DomMulAct.mk.symm (fun g => by
        exact DomMulAct.mem_stabilizer_iff)
    rw [Fintype.card_congr e]
    exact DomMulAct.stabilizer_card f
  have hG : Fintype.card G = (Fintype.card α).factorial := by
    exact Fintype.card_congr DomMulAct.mk.symm |>.trans Fintype.card_perm
  change Fintype.card {g : α → ι // P g} = _
  rw [← hstab]
  exact Nat.eq_div_of_mul_eq_left (Fintype.card_ne_zero)
    (by simpa [hG] using horbitCard)

end

section
-- Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open Equiv

set_option autoImplicit false

/-- A finite histogram whose total is the domain size is realizable, and the
corresponding functions are counted by the multinomial coefficient. -/
theorem mme_fintype_prescribed_fiber_function_card
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (k : ι → ℕ) (hsum : ∑ i, k i = Fintype.card α) :
    Fintype.card
        {g : α → ι // ∀ i,
          Fintype.card {a // g a = i} = k i} =
      (Fintype.card α).factorial / ∏ i, (k i).factorial := by
  classical
  let β := Σ i : ι, Fin (k i)
  let e : α ≃ β := Fintype.equivOfCardEq (by
    rw [Fintype.card_sigma]
    simpa using hsum.symm)
  let f : α → ι := fun a => (e a).1
  have hfiber : ∀ i,
      Fintype.card {a // f a = i} = k i := by
    intro i
    let e₁ : {a // f a = i} ≃ {b : β // b.1 = i} :=
      Equiv.subtypeEquiv e (fun a => by rfl)
    calc
      Fintype.card {a // f a = i} =
          Fintype.card {b : β // b.1 = i} := Fintype.card_congr e₁
      _ = Fintype.card (Fin (k i)) :=
        Fintype.card_congr (Equiv.sigmaSubtype i)
      _ = k i := Fintype.card_fin _
  let profileEquiv :
      {g : α → ι // ∀ i, Fintype.card {a // g a = i} = k i} ≃
      {g : α → ι // ∀ i,
        Fintype.card {a // g a = i} =
          Fintype.card {a // f a = i}} :=
    Equiv.subtypeEquiv (Equiv.refl (α → ι)) (fun g => by
      constructor
      · intro hg i
        simpa only [hfiber] using hg i
      · intro hg i
        simpa only [hfiber] using hg i)
  rw [Fintype.card_congr profileEquiv,
    mme_fintype_fixed_fiber_function_card f]
  apply congrArg ((Fintype.card α).factorial / ·)
  apply Finset.prod_congr rfl
  intro i hi
  rw [hfiber]

end

section
-- Theorems.Thm_mme_recursive_yz_boundary_exact_code_card

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem scalarBundle7_count_lifts {X S : Type*} [Fintype X] [Fintype S] [DecidableEq S]
    (label : X → S) (L : ℕ) (mu : S → ℕ) (hsum : ∑ s, mu s = L) :
    Fintype.card {x : Fin L → X // ∀ s,
      Fintype.card {p : Fin L // label (x p) = s} = mu s} =
      (L.factorial / ∏ s, (mu s).factorial) *
        ∏ s, (Fintype.card {a : X // label a = s}) ^ mu s := by
  classical
  let F := {f : Fin L → S // ∀ s, Fintype.card {p // f p = s} = mu s}
  let E : {x : Fin L → X // ∀ s,
      Fintype.card {p : Fin L // label (x p) = s} = mu s} ≃
      (Σ f : F, ∀ p, {a : X // label a = f.val p}) := {
    toFun := fun x ↦ ⟨⟨fun p ↦ label (x.val p), x.property⟩, fun p ↦ ⟨x.val p, rfl⟩⟩
    invFun := fun y ↦ ⟨fun p ↦ (y.2 p).val, by
      intro s
      have h : (fun p ↦ label (y.2 p).val) = y.1.val :=
        funext (fun p ↦ (y.2 p).property)
      exact (Fintype.card_congr (Equiv.subtypeEquivRight
        (fun p ↦ by rw [(y.2 p).property]))).trans (y.1.property s)⟩
    left_inv := by intro x; rfl
    right_inv := by
      intro y
      rcases y with ⟨⟨f,hf⟩,x⟩
      have h : (fun p ↦ label (x p).val) = f := funext (fun p ↦ (x p).property)
      apply Sigma.ext (Subtype.ext h)
      apply Function.hfunext rfl
      intro p p' hp
      cases hp
      exact (Subtype.heq_iff_coe_eq (fun a ↦ by
        change label a = label (x p).val ↔ label a = f p
        rw [(x p).property])).mpr rfl }
  rw [Fintype.card_congr E, Fintype.card_sigma]
  have hp (f : F) : (∏ p, Fintype.card {a : X // label a = f.val p}) =
      ∏ s, (Fintype.card {a : X // label a = s}) ^ mu s := by
    calc
      _ = ∏ s, ∏ _p : {p // f.val p = s}, Fintype.card {a : X // label a = s} :=
        (Fintype.prod_fiberwise' f.val (fun s ↦ Fintype.card {a : X // label a = s})).symm
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, f.property]
  simp_rw [Fintype.card_pi, hp]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simpa [F] using mme_fintype_prescribed_fiber_function_card (α := Fin L) mu (by simpa using hsum)

private theorem scalarBundle7_label_fiber_card (ell : ℕ) (s : CompleteWord ell) :
    Fintype.card {x : Letters ell // labels x = s} = 5 ^ ones s := by
  classical
  let E : {x : Letters ell // labels x = s} ≃
      (∀ r, {a : Fin 7 // MME.cwSquareCoordGrade 5 a = s r}) := {
    toFun := fun x r ↦ ⟨x.val r, congrFun x.property r⟩
    invFun := fun x ↦ ⟨fun r ↦ (x r).val, funext (fun r ↦ (x r).property)⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  rw [Fintype.card_congr E, Fintype.card_pi]
  have hc (a : Fin 3) : Fintype.card {x : Fin 7 // MME.cwSquareCoordGrade 5 x = a} =
      if a = 1 then 5 else 1 := by fin_cases a <;> decide
  simp_rw [hc]
  rw [Finset.prod_ite]
  simp [ones]

theorem mme_recursive_yz_boundary_exact_code_card {ell L : ℕ} (B : MME.RecursiveYZ.Boundary.Profile ell L) :
    Fintype.card (Code ell L B.count) = B.dim := by
  classical
  rw [show Fintype.card (Code ell L B.count) = _ from
    scalarBundle7_count_lifts (@labels ell) L B.count B.total]
  simp_rw [scalarBundle7_label_fiber_card, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [MME.RecursiveYZ.Boundary.Profile.dim, Nat.mul_comm]

end

section
-- Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
open MME MME.CompleteSplit MME.TensorObj PiTensorProduct TensorProduct BigOperators Module
  MME.DWZStep1Support MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 900000
set_option maxRecDepth 2000
universe u

private theorem scalarBundle8_interchange_tprod_explicit
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

private theorem scalarBundle8_interchange_basis_repr_explicit
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
          simp [scalarBundle8_interchange_tprod_explicit, Finset.prod_mul_distrib]
          ring
      | add y z hy hz =>
          simp only [map_add, Finsupp.add_apply, mul_add, hy, hz]
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, Finsupp.add_apply,
        add_mul, hx, hz]

private theorem scalarBundle8_piTensorProduct_basis_reindex_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    {ι κ : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (V i))
    (e : ∀ i, ι i ≃ κ i) :
    Basis.piTensorProduct (fun i ↦ (b i).reindex (e i)) =
      (Basis.piTensorProduct b).reindex (Equiv.piCongrRight e) := by
  ext w
  simp [Basis.piTensorProduct_apply,
    Module.Basis.reindex_apply]

private theorem scalarBundle8_basis_repr_equiv_explicit
    {K : Type u} [Field K]
    {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {ι κ : Type u} (B : Basis ι K V) (C : Basis κ K W) (E : ι ≃ κ)
    (x : V) (w : κ) :
    C.repr (B.equiv C E x) w = B.repr x (E.symm w) := by
  have h := congrArg (fun f : ι →₀ K ↦ f (E.symm w))
    ((C.reindex E.symm).repr.apply_symm_apply (B.repr x))
  change (C.reindex E.symm).repr
    ((C.reindex E.symm).repr.symm (B.repr x)) (E.symm w) = B.repr x (E.symm w) at h
  rw [Module.Basis.repr_reindex_apply] at h
  simpa [Module.Basis.equiv, LinearEquiv.trans_apply] using h

@[simp]
private theorem scalarBundle8_kronPowModeWordBasis_succ_apply_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) (i : Fin d) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ) (w : Fin (n + 1) → ι) :
    kronPowModeWordBasis T i b (n + 1) w =
      b (w 0) ⊗ₜ[K]
        kronPowModeWordBasis T i b n (fun r ↦ w r.succ) := by
  rw [kronPowModeWordBasis]
  calc
    _ = (Module.Basis.tensorProduct b
          (kronPowModeWordBasis T i b n))
        ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι)).symm w) :=
      Module.Basis.reindex_apply _ _ _
    _ = _ := by
      rw [Fin.consEquiv_symm_apply,
        Module.Basis.tensorProduct_apply]
      rfl

private noncomputable def scalarBundle8_kronPowTensorWordBasisExplicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i)) (n : ℕ) :
    Basis (∀ i, Fin n → ι i) K
      (PiTensorProduct K (fun i ↦ (T.kronPow n).V i)) :=
  Basis.piTensorProduct
    (fun i ↦ kronPowModeWordBasis T i (b i) n)

private theorem scalarBundle8_kronPowTensorWordBasis_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (n : ℕ) (w : ∀ i, Fin n → ι i) :
    (scalarBundle8_kronPowTensorWordBasisExplicit T b n).repr (T.kronPow n).t w =
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
      rw [scalarBundle8_piTensorProduct_basis_reindex_explicit]
      rw [Module.Basis.repr_reindex_apply]
      rw [scalarBundle8_interchange_basis_repr_explicit]
      simp only [Equiv.piCongrRight_symm_apply,
        Pi.map_apply, Fin.consEquiv_symm_apply]
      change
        (Basis.piTensorProduct b).repr T.t (fun i ↦ w i 0) *
          (scalarBundle8_kronPowTensorWordBasisExplicit T b n).repr (T.kronPow n).t
            (fun i r ↦ w i r.succ) = _
      rw [ih]
      rw [Fin.prod_univ_succ]


private theorem scalarBundle8_select_coeff_restrict
    {K : Type u} [Field K] (T S : TensorObj K 3)
    {I : Fin 3 → Type u} {J : Fin 3 → Type}
    [∀ i, Fintype (J i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (c : ∀ i, Basis (J i) K (S.V i))
    (allowed : ∀ i, I i → Prop) (e : ∀ i, J i → I i)
    (he : ∀ i j, allowed i (e i j))
    (hc : ∀ w, (Basis.piTensorProduct b).repr T.t (fun i ↦ e i (w i)) =
      (Basis.piTensorProduct c).repr S.t w) :
    Restrict S (T.basisAllAllowedSubtensor b allowed) := by
  classical
  let f := fun i ↦ (c i).equivFun.symm.toLinearMap.comp
    (LinearMap.pi (fun j ↦ (b i).coord (e i j)))
  have hf (i : Fin 3) (x : T.V i) (j : J i) :
      (c i).repr (f i x) j = (b i).repr x (e i j) := by
    change (c i).coord j ((c i).equivFun.symm _) = _
    rw [Basis.coord_equivFun_symm]
    rfl
  have hmap (x : PiTensorProduct K T.V) (w : ∀ i, J i) :
      (Basis.piTensorProduct c).repr (PiTensorProduct.map f x) w =
        (Basis.piTensorProduct b).repr x (fun i ↦ e i (w i)) := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      simp only [map_smul, PiTensorProduct.map_tprod,
        Basis.piTensorProduct_repr_tprod_apply, Finsupp.smul_apply, hf]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes T S b allowed f
  · apply (Basis.piTensorProduct c).repr.injective
    ext w
    exact (hmap T.t w).trans (hc w)
  · intro i x hx
    apply (c i).repr.injective
    ext j
    rw [hf]
    have hne : x ≠ e i j := fun h ↦ hx (h ▸ he i j)
    simp [hne]

private def scalarBundle8_triple (z : Fin 3) (a b : Fin 7) : Fin 3 → ULift.{u} (Fin 7) :=
  if z = 0 then ![⟨0⟩, ⟨a⟩, ⟨MME.RecursiveYZ.Boundary.flip b⟩]
  else if z = 1 then ![⟨MME.RecursiveYZ.Boundary.flip b⟩, ⟨0⟩, ⟨a⟩]
  else ![⟨a⟩, ⟨MME.RecursiveYZ.Boundary.flip b⟩, ⟨0⟩]

private noncomputable def scalarBundle8_bbase (K : Type u) [Field K] :
    ∀ i : Fin 3, Basis (ULift.{u} (Fin 7)) K ((CWObj K 5).V i) :=
  fun i ↦ (cwThreeCanonicalBasis K 5 i).reindex Equiv.ulift.symm

private theorem scalarBundle8_monom_basis {K : Type u} [Field K] (a b c : Fin 7) :
    CWMonom K 5 a b c = (Basis.piTensorProduct (scalarBundle8_bbase K)) ![ULift.up a,ULift.up b,ULift.up c] := by
  rw [Basis.piTensorProduct_apply]
  unfold CWMonom
  congr 1
  funext i
  fin_cases i <;> dsimp only [scalarBundle8_bbase, cwThreeCanonicalBasis] <;>
    rw [Basis.reindex_apply]
  · exact (Pi.basisFun_apply K (Fin 7) a).symm
  · exact (Pi.basisFun_apply K (Fin 7) b).symm
  · exact (Pi.basisFun_apply K (Fin 7) c).symm

private theorem scalarBundle8_base_expansion {K : Type u} [Field K] :
    (CWObj K 5).t =
      (∑ k : Fin 5, (
        (Basis.piTensorProduct (scalarBundle8_bbase K)) ![ULift.up 0,ULift.up (⟨k.val+1,by omega⟩ : Fin 7),ULift.up ⟨k.val+1,by omega⟩] +
        (Basis.piTensorProduct (scalarBundle8_bbase K)) ![ULift.up ⟨k.val+1,by omega⟩,ULift.up 0,ULift.up ⟨k.val+1,by omega⟩] +
        (Basis.piTensorProduct (scalarBundle8_bbase K)) ![ULift.up ⟨k.val+1,by omega⟩,ULift.up ⟨k.val+1,by omega⟩,ULift.up 0])) +
      (Basis.piTensorProduct (scalarBundle8_bbase K)) ![ULift.up 0,ULift.up 0,ULift.up 6] +
      (Basis.piTensorProduct (scalarBundle8_bbase K)) ![ULift.up 0,ULift.up 6,ULift.up 0] +
      (Basis.piTensorProduct (scalarBundle8_bbase K)) ![ULift.up 6,ULift.up 0,ULift.up 0] := by
  simp only [← scalarBundle8_monom_basis]
  rfl

private theorem scalarBundle8_base_coeff {K : Type u} [Field K] (z : Fin 3) (a b : Fin 7) :
    (Basis.piTensorProduct (scalarBundle8_bbase K)).repr
      (CWObj K 5).t (scalarBundle8_triple.{u} z a b) = if a = b then 1 else 0 := by
  classical
  have h := scalarBundle8_base_expansion (K := K)
  generalize (Basis.piTensorProduct (scalarBundle8_bbase K)) = BB at h ⊢
  rw [h]
  simp only [map_add, map_sum, Finsupp.finset_sum_apply, Finsupp.add_apply,
    Basis.repr_self, Finsupp.single_apply]
  clear h
  simp only [Fin.sum_univ_succ]
  fin_cases z <;> fin_cases a <;> fin_cases b <;>
    norm_num [scalarBundle8_triple, MME.RecursiveYZ.Boundary.flip, Equiv.swap_apply_def,
      Matrix.vecCons_inj, ULift.ext_iff]
  all_goals norm_num [Fin.ext_iff]

private theorem scalarBundle8_power_coeff {K : Type u} [Field K] (ell L : ℕ) (z : Fin 3)
    (x y : Fin (L * 2 ^ (ell - 1)) → Fin 7) :
    (Basis.piTensorProduct (basis K 5 ell L)).repr (source K 5 ell L).t
      (fun i r ↦ scalarBundle8_triple z (x r) (y r) i) = if x = y then 1 else 0 := by
  classical
  refine (scalarBundle8_kronPowTensorWordBasis_repr_explicit (CWObj K 5) (scalarBundle8_bbase K)
    (L * 2 ^ (ell - 1)) (fun i r ↦ scalarBundle8_triple.{u} z (x r) (y r) i)).trans ?_
  have hb (a b : Fin 7) := scalarBundle8_base_coeff (K := K) z a b
  generalize (Basis.piTensorProduct (scalarBundle8_bbase K)).repr (CWObj K 5).t = coeff at hb ⊢
  change (∏ r, coeff (scalarBundle8_triple.{u} z (x r) (y r))) = _
  simp only [hb]
  by_cases h : x = y
  · subst y; simp
  · rw [if_neg h]
    obtain ⟨r,hr⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ r) (if_neg hr)

private def scalarBundle8_flat {ell L : ℕ} {mu : CompleteWord ell → ℕ}
    (x : Code ell L mu) (r : Fin (L * 2 ^ (ell - 1))) : Fin 7 :=
  x.val (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2

private theorem scalarBundle8_flat_injective {ell L : ℕ} {mu : CompleteWord ell → ℕ} :
    Function.Injective (@scalarBundle8_flat ell L mu) := by
  intro x y h
  apply Subtype.ext
  funext p r
  have := congrFun h (finProdFinEquiv (p,r))
  simpa [scalarBundle8_flat] using this

private theorem scalarBundle8_flip_grade (a : Fin 7) :
    cwSquareCoordGrade 5 (MME.RecursiveYZ.Boundary.flip a) =
      ⟨2 - (cwSquareCoordGrade 5 a).val, by omega⟩ := by
  fin_cases a <;> decide

private theorem scalarBundle8_flipLabel_twice {ell : ℕ} (s : CompleteWord ell) :
    flipLabel (flipLabel s) = s := by
  funext r
  apply Fin.ext
  simp only [flipLabel]
  omega

private theorem scalarBundle8_grade_flipLabel {ell : ℕ} (s : CompleteWord ell) :
    MME.RecursiveYZ.CWCells.grade (flipLabel s) = 2 * 2 ^ (ell - 1) - MME.RecursiveYZ.CWCells.grade s := by
  unfold MME.RecursiveYZ.CWCells.grade flipLabel
  rw [Finset.sum_tsub_distrib]
  · simp [mul_comm]
  · intro r _; exact Nat.le_of_lt_succ (s r).isLt

private theorem scalarBundle8_code_grade {ell L : ℕ} (B : MME.RecursiveYZ.Boundary.Profile ell L)
    (x : Code ell L B.count) (p : Fin L) : MME.RecursiveYZ.CWCells.grade (labels (x.val p)) = B.index := by
  apply B.supported
  have h := x.property (labels (x.val p))
  have hp : 0 < Fintype.card {r : Fin L // labels (x.val r) = labels (x.val p)} :=
    Fintype.card_pos_iff.mpr ⟨⟨p,rfl⟩⟩
  omega

private theorem scalarBundle8_label_flat {ell L : ℕ} {mu : CompleteWord ell → ℕ}
    (x : Code ell L mu) (p : Fin L) :
    label 5 ell L (Equiv.refl _) (fun r ↦ (⟨scalarBundle8_flat x r⟩ : ULift.{u} (Fin 7))) p = labels (x.val p) := by
  funext r
  simp [label, scalarBundle8_flat, labels]

private theorem scalarBundle8_label_flip_flat {ell L : ℕ} {mu : CompleteWord ell → ℕ}
    (x : Code ell L mu) (p : Fin L) :
    label 5 ell L (Equiv.refl _) (fun r ↦ (⟨MME.RecursiveYZ.Boundary.flip (scalarBundle8_flat x r)⟩ : ULift.{u} (Fin 7))) p =
      flipLabel (labels (x.val p)) := by
  funext r
  simp [label, scalarBundle8_flat, labels, flipLabel, scalarBundle8_flip_grade]

private theorem scalarBundle8_zero_allowed {ell L : ℕ} (_B : MME.RecursiveYZ.Boundary.Profile ell L) :
    allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ _ ↦ 0) (fun _ _ s ↦ if s = (fun _ ↦ 0) then L else 0) 0
      (fun _ ↦ (⟨0⟩ : ULift.{u} (Fin 7))) := by
  classical
  constructor
  · intro p; simp [label, MME.RecursiveYZ.CWCells.grade, cwSquareCoordGrade]
  · intro c s
    cases c
    have hl (p : Fin L) : label 5 ell L (Equiv.refl _) (fun _ ↦ (⟨0⟩ : ULift.{u} (Fin 7))) p = (fun _ ↦ 0) := by
      funext r; rfl
    simp only [MME.RecursiveYZ.count, hl, true_and]
    by_cases hs : s = (fun _ ↦ 0)
    · subst s; simp only [hl, eq_self, Finset.filter_true, Finset.card_univ, Fintype.card_fin, if_true]
    · simp only [hl, hs, Ne.symm hs, if_false, Finset.filter_false, Finset.card_empty]

private theorem scalarBundle8_free_allowed {ell L : ℕ} (B : MME.RecursiveYZ.Boundary.Profile ell L)
    (x : Code ell L B.count) :
    allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ _ ↦ B.index) (fun _ _ ↦ B.count) 0 (fun r ↦ (⟨scalarBundle8_flat x r⟩ : ULift.{u} (Fin 7))) := by
  classical
  constructor
  · intro p; rw [scalarBundle8_label_flat]; exact scalarBundle8_code_grade B x p
  · intro c s
    cases c
    simpa [MME.RecursiveYZ.count, scalarBundle8_label_flat, Fintype.card_subtype] using x.property s

private theorem scalarBundle8_flipped_allowed {ell L : ℕ} (B : MME.RecursiveYZ.Boundary.Profile ell L)
    (x : Code ell L B.count) :
    allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ _ ↦ 2 * 2 ^ (ell - 1) - B.index)
      (fun _ _ s ↦ B.count (flipLabel s)) 0
      (fun r ↦ (⟨MME.RecursiveYZ.Boundary.flip (scalarBundle8_flat x r)⟩ : ULift.{u} (Fin 7))) := by
  classical
  constructor
  · intro p; rw [scalarBundle8_label_flip_flat, scalarBundle8_grade_flipLabel, scalarBundle8_code_grade]
  · intro c s
    cases c
    have hf (p : Fin L) : flipLabel (labels (x.val p)) = s ↔ labels (x.val p) = flipLabel s := by
      constructor
      · intro h; have := congrArg flipLabel h; simpa [scalarBundle8_flipLabel_twice] using this
      · intro h; rw [h, scalarBundle8_flipLabel_twice]
    simpa [MME.RecursiveYZ.count, scalarBundle8_label_flip_flat, hf, Fintype.card_subtype] using
      x.property (flipLabel s)

private def scalarBundle8_mmIndex (a b c : ℕ) : Fin 3 → Type
  | ⟨0,_⟩ => Fin a × Fin b
  | ⟨1,_⟩ => Fin b × Fin c
  | ⟨2,_⟩ => Fin c × Fin a

private instance scalarBundle8_mmIndexFintype (a b c : ℕ) (i : Fin 3) : Fintype (scalarBundle8_mmIndex a b c i) :=
  match i with
  | ⟨0,_⟩ => by change Fintype (Fin a × Fin b); infer_instance
  | ⟨1,_⟩ => by change Fintype (Fin b × Fin c); infer_instance
  | ⟨2,_⟩ => by change Fintype (Fin c × Fin a); infer_instance

private noncomputable def scalarBundle8_mmBasis (K : Type u) [Field K] (a b c : ℕ) (i : Fin 3) :
    Basis (scalarBundle8_mmIndex a b c i) K (MMSpace K a b c i) :=
  match i with
  | ⟨0,_⟩ => Pi.basisFun K (Fin a × Fin b)
  | ⟨1,_⟩ => Pi.basisFun K (Fin b × Fin c)
  | ⟨2,_⟩ => Pi.basisFun K (Fin c × Fin a)

private theorem scalarBundle8_mm_repr0 {K : Type u} [Field K] (a b c : ℕ)
    (x : MMSpace K a b c 0) (j : scalarBundle8_mmIndex a b c 0) :
    (scalarBundle8_mmBasis K a b c 0).repr x j = x j := by
  exact Pi.basisFun_repr K (Fin a × Fin b) x j

private theorem scalarBundle8_mm_repr1 {K : Type u} [Field K] (a b c : ℕ)
    (x : MMSpace K a b c 1) (j : scalarBundle8_mmIndex a b c 1) :
    (scalarBundle8_mmBasis K a b c 1).repr x j = x j := by
  exact Pi.basisFun_repr K (Fin b × Fin c) x j

private theorem scalarBundle8_mm_repr2 {K : Type u} [Field K] (a b c : ℕ)
    (x : MMSpace K a b c 2) (j : scalarBundle8_mmIndex a b c 2) :
    (scalarBundle8_mmBasis K a b c 2).repr x j = x j := by
  exact Pi.basisFun_repr K (Fin c × Fin a) x j

private theorem scalarBundle8_mm_coeff0 {K : Type u} [Field K] (M : ℕ) (w : ∀ i, scalarBundle8_mmIndex 1 1 M i) :
    (Basis.piTensorProduct (scalarBundle8_mmBasis K 1 1 M)).repr (MMObj K 1 1 M).t w =
      if (w 1).2 = (w 2).1 then 1 else 0 := by
  classical
  change (Basis.piTensorProduct (scalarBundle8_mmBasis K 1 1 M)).repr (MMTensor K 1 1 M) w = _
  simp only [MMTensor, map_sum, Finsupp.finset_sum_apply]
  simp only [Basis.piTensorProduct_repr_tprod_apply]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (∑ i : Fin 1, ∑ j : Fin 1, ∑ k : Fin M,
    (scalarBundle8_mmBasis K 1 1 M 0).repr (Pi.single (i,j) 1) (w 0) *
      ((scalarBundle8_mmBasis K 1 1 M 1).repr (Pi.single (j,k) 1) (w 1) *
        (scalarBundle8_mmBasis K 1 1 M 2).repr (Pi.single (k,i) 1) (w 2))) = _
  simp only [scalarBundle8_mm_repr0 (K := K) 1 1 M, scalarBundle8_mm_repr1 (K := K) 1 1 M, scalarBundle8_mm_repr2 (K := K) 1 1 M]
  simp [Fin.eq_zero, Pi.single_apply, Prod.ext_iff, eq_comm, ite_mul, mul_ite]

private theorem scalarBundle8_mm_coeff1 {K : Type u} [Field K] (M : ℕ) (w : ∀ i, scalarBundle8_mmIndex M 1 1 i) :
    (Basis.piTensorProduct (scalarBundle8_mmBasis K M 1 1)).repr (MMObj K M 1 1).t w =
      if (w 2).2 = (w 0).1 then 1 else 0 := by
  classical
  change (Basis.piTensorProduct (scalarBundle8_mmBasis K M 1 1)).repr (MMTensor K M 1 1) w = _
  simp only [MMTensor, map_sum, Finsupp.finset_sum_apply]
  simp only [Basis.piTensorProduct_repr_tprod_apply]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (∑ i : Fin M, ∑ j : Fin 1, ∑ k : Fin 1,
    (scalarBundle8_mmBasis K M 1 1 0).repr (Pi.single (i,j) 1) (w 0) *
      ((scalarBundle8_mmBasis K M 1 1 1).repr (Pi.single (j,k) 1) (w 1) *
        (scalarBundle8_mmBasis K M 1 1 2).repr (Pi.single (k,i) 1) (w 2))) = _
  simp only [scalarBundle8_mm_repr0 (K := K) M 1 1, scalarBundle8_mm_repr1 (K := K) M 1 1, scalarBundle8_mm_repr2 (K := K) M 1 1]
  simp [Fin.eq_zero, Pi.single_apply, Prod.ext_iff, eq_comm, ite_mul, mul_ite]

private theorem scalarBundle8_mm_coeff2 {K : Type u} [Field K] (M : ℕ) (w : ∀ i, scalarBundle8_mmIndex 1 M 1 i) :
    (Basis.piTensorProduct (scalarBundle8_mmBasis K 1 M 1)).repr (MMObj K 1 M 1).t w =
      if (w 0).2 = (w 1).1 then 1 else 0 := by
  classical
  change (Basis.piTensorProduct (scalarBundle8_mmBasis K 1 M 1)).repr (MMTensor K 1 M 1) w = _
  simp only [MMTensor, map_sum, Finsupp.finset_sum_apply]
  simp only [Basis.piTensorProduct_repr_tprod_apply]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (∑ i : Fin 1, ∑ j : Fin M, ∑ k : Fin 1,
    (scalarBundle8_mmBasis K 1 M 1 0).repr (Pi.single (i,j) 1) (w 0) *
      ((scalarBundle8_mmBasis K 1 M 1 1).repr (Pi.single (j,k) 1) (w 1) *
        (scalarBundle8_mmBasis K 1 M 1 2).repr (Pi.single (k,i) 1) (w 2))) = _
  simp only [scalarBundle8_mm_repr0 (K := K) 1 M 1, scalarBundle8_mm_repr1 (K := K) 1 M 1, scalarBundle8_mm_repr2 (K := K) 1 M 1]
  simp [Fin.eq_zero, Pi.single_apply, Prod.ext_iff, eq_comm, ite_mul, mul_ite]

theorem mme_recursive_yz_boundary_actual_matrix_extraction {K : Type u} [Field K] {ell L : ℕ}
    (B : MME.RecursiveYZ.Boundary.Profile ell L) (z : Fin 3) :
    Restrict (MMObj K (B.a z) (B.b z) (B.c z)) (B.tensor K z) := by
  classical
  let M := Fintype.card (Code ell L B.count)
  have hd : B.dim = M := (mme_recursive_yz_boundary_exact_code_card B).symm
  let E : Fin M ≃ Code ell L B.count := (Fintype.equivFin _).symm
  have hE : Function.Injective (fun j : Fin M ↦ scalarBundle8_flat (E j)) :=
    scalarBundle8_flat_injective.comp E.injective
  have hz := scalarBundle8_zero_allowed.{u} B
  fin_cases z
  · change Restrict (MMObj K 1 1 B.dim) (B.tensor K 0)
    rw [hd]
    let e : ∀ i, scalarBundle8_mmIndex 1 1 M i → WordIndex.{u} 5 ell L := by
      intro i
      match i with
      | ⟨0,_⟩ => exact fun j r ↦ ULift.up (0)
      | ⟨1,_⟩ => exact fun j r ↦ ULift.up (scalarBundle8_flat (E j.2) r)
      | ⟨2,_⟩ => exact fun j r ↦ ULift.up (MME.RecursiveYZ.Boundary.flip (scalarBundle8_flat (E j.1) r))
    apply scalarBundle8_select_coeff_restrict (source K 5 ell L) (MMObj K 1 1 M)
      (basis K 5 ell L) (scalarBundle8_mmBasis K 1 1 M)
      (allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ B.shape 0) (fun i _ ↦ B.mu 0 i)) e
    · intro i j
      fin_cases i
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (hz)
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (scalarBundle8_free_allowed.{u} B (E j.2))
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (scalarBundle8_flipped_allowed.{u} B (E j.1))
    · intro w
      have heq : (fun i ↦ e i (w i)) =
          (fun i r ↦ scalarBundle8_triple 0 (scalarBundle8_flat (E (w 1).2) r) (scalarBundle8_flat (E (w 2).1) r) i) := by
        funext i r
        fin_cases i <;> rfl
      rw [heq, scalarBundle8_power_coeff]
      simpa only [hE.eq_iff] using (scalarBundle8_mm_coeff0 (K := K) M w).symm
  · change Restrict (MMObj K B.dim 1 1) (B.tensor K 1)
    rw [hd]
    let e : ∀ i, scalarBundle8_mmIndex M 1 1 i → WordIndex.{u} 5 ell L := by
      intro i
      match i with
      | ⟨0,_⟩ => exact fun j r ↦ ULift.up (MME.RecursiveYZ.Boundary.flip (scalarBundle8_flat (E j.1) r))
      | ⟨1,_⟩ => exact fun j r ↦ ULift.up (0)
      | ⟨2,_⟩ => exact fun j r ↦ ULift.up (scalarBundle8_flat (E j.2) r)
    apply scalarBundle8_select_coeff_restrict (source K 5 ell L) (MMObj K M 1 1)
      (basis K 5 ell L) (scalarBundle8_mmBasis K M 1 1)
      (allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ B.shape 1) (fun i _ ↦ B.mu 1 i)) e
    · intro i j
      fin_cases i
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (scalarBundle8_flipped_allowed.{u} B (E j.1))
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (hz)
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (scalarBundle8_free_allowed.{u} B (E j.2))
    · intro w
      have heq : (fun i ↦ e i (w i)) =
          (fun i r ↦ scalarBundle8_triple 1 (scalarBundle8_flat (E (w 2).2) r) (scalarBundle8_flat (E (w 0).1) r) i) := by
        funext i r
        fin_cases i <;> rfl
      rw [heq, scalarBundle8_power_coeff]
      simpa only [hE.eq_iff] using (scalarBundle8_mm_coeff1 (K := K) M w).symm
  · change Restrict (MMObj K 1 B.dim 1) (B.tensor K 2)
    rw [hd]
    let e : ∀ i, scalarBundle8_mmIndex 1 M 1 i → WordIndex.{u} 5 ell L := by
      intro i
      match i with
      | ⟨0,_⟩ => exact fun j r ↦ ULift.up (scalarBundle8_flat (E j.2) r)
      | ⟨1,_⟩ => exact fun j r ↦ ULift.up (MME.RecursiveYZ.Boundary.flip (scalarBundle8_flat (E j.1) r))
      | ⟨2,_⟩ => exact fun j r ↦ ULift.up (0)
    apply scalarBundle8_select_coeff_restrict (source K 5 ell L) (MMObj K 1 M 1)
      (basis K 5 ell L) (scalarBundle8_mmBasis K 1 M 1)
      (allowed 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ B.shape 2) (fun i _ ↦ B.mu 2 i)) e
    · intro i j
      fin_cases i
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (scalarBundle8_free_allowed.{u} B (E j.2))
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (scalarBundle8_flipped_allowed.{u} B (E j.1))
      · simpa [e, allowed, MME.RecursiveYZ.Boundary.Profile.shape,
          MME.RecursiveYZ.Boundary.Profile.mu] using (hz)
    · intro w
      have heq : (fun i ↦ e i (w i)) =
          (fun i r ↦ scalarBundle8_triple 2 (scalarBundle8_flat (E (w 0).2) r) (scalarBundle8_flat (E (w 1).1) r) i) := by
        funext i r
        fin_cases i <;> rfl
      rw [heq, scalarBundle8_power_coeff]
      simpa only [hE.eq_iff] using (scalarBundle8_mm_coeff2 (K := K) M w).symm

end

section
-- Theorems.Thm_mme_kronFin_MMObj_iso

open MME BigOperators

universe u

theorem mme_kronFin_MMObj_iso
    {K : Type u} [Field K] :
    ∀ (R : ℕ) (a b c : Fin R → ℕ),
      TensorObj.Isomorphic
        (TensorObj.kronFin R (fun r => MMObj K (a r) (b r) (c r)))
        (MMObj K (∏ r, a r) (∏ r, b r) (∏ r, c r)) := by
  intro R
  induction R with
  | zero =>
      intro a b c
      simp only [TensorObj.kronFin]
      have hq :
          TensorQ.toQ (TensorObj.oneObj : TensorObj K 3) =
            TensorQ.toQ (MMObj K 1 1 1) := by
        exact (MMq_one (K := K)).symm
      exact Quotient.exact hq
  | succ R ih =>
      intro a b c
      let af : Fin R → ℕ := fun r => a r.succ
      let bf : Fin R → ℕ := fun r => b r.succ
      let cf : Fin R → ℕ := fun r => c r.succ
      have htail := ih af bf cf
      have hkron : TensorObj.Isomorphic
          (TensorObj.kron (MMObj K (a 0) (b 0) (c 0))
            (TensorObj.kronFin R
              (fun r => MMObj K (af r) (bf r) (cf r))))
          (TensorObj.kron (MMObj K (a 0) (b 0) (c 0))
            (MMObj K (∏ r, af r) (∏ r, bf r) (∏ r, cf r))) :=
        TensorQ.mul_respects_iso (TensorObj.Isomorphic.refl _) htail
      have hmm := MMObj_kron_iso (K := K)
        (a 0) (b 0) (c 0)
        (∏ r, af r) (∏ r, bf r) (∏ r, cf r)
      simpa only [TensorObj.kronFin, af, bf, cf, Fin.prod_univ_succ] using
        hkron.trans hmm


end

section
-- Theorems.Thm_mme_recursive_profiled_CW_boundary_end

open MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.CompleteSplit Module BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
universe u

private theorem scalarBundle10_tensor_cast {K : Type u} [Field K] {n m : ℕ} (h : n = m)
    (P : Predicate m) :
    tensor K (fun i (x : FineWord n) ↦ P i (fun j ↦ x (Fin.cast h.symm j))) = tensor K P := by
  subst m
  rfl

private theorem scalarBundle10_split_cast {S : Type} {ell L N : ℕ} (p : Fin L ≃ S)
    (h : L * 2 ^ (ell - 1) = N) (x : WordIndex.{u} 5 ell L) :
    split p h (fun j ↦ fine x (Fin.cast h.symm j)) = CWCells.label 5 ell L p x := by
  funext s r
  simp [split, CWCells.label, fine]

theorem mme_recursive_profiled_CW_boundary_end {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (B : BoundaryEnd ell N P) :
    Restrict (MMObj K B.a B.b B.c) (tensor K P) := by
  let parts := B.partition
  let child := parts.piece K 5 ell B.shape B.mu
  let a := fun j ↦ (B.profile j).a (B.zeroMode j)
  let b := fun j ↦ (B.profile j).b (B.zeroMode j)
  let c := fun j ↦ (B.profile j).c (B.zeroMode j)
  have hc (j) : Restrict (MMObj K (a j) (b j) (c j)) (child j) := by
    have heq : child j = (B.profile j).tensor K (B.zeroMode j) := by
      simp only [child, parts, Partition.piece, Boundary.Profile.tensor, B.shapes, B.profiles]
    rw [heq]
    exact mme_recursive_yz_boundary_actual_matrix_extraction (B.profile j) (B.zeroMode j)
  choose maps hm using hc
  have hprod : Restrict (kronFin parts.parts (fun j ↦ MMObj K (a j) (b j) (c j)))
      (kronFin parts.parts child) :=
    ⟨kronFinFamilyModeMap parts.parts child (fun j ↦ MMObj K (a j) (b j) (c j)) maps,
      kronFinFamilyModeMap_preserves_tensor child _ maps hm⟩
  have hboundary : Restrict (MMObj K B.a B.b B.c)
      (unbroken K 5 ell B.L (Equiv.refl _) B.cell B.shape B.mu) :=
    (mme_kronFin_MMObj_iso parts.parts a b c).2.trans
      (hprod.trans (mme_recursive_yz_actual_cell_product_restriction
        5 ell B.L (Equiv.refl _) B.cell B.shape B.mu parts))
  let pull : Predicate (B.L * 2 ^ (ell - 1)) :=
    fun i x ↦ P i (fun j ↦ x (Fin.cast B.length.symm j))
  have hmono : Restrict (unbroken K 5 ell B.L (Equiv.refl _) B.cell B.shape B.mu)
      (tensor K pull) := by
    apply mme_basis_projected_family_restrict (CWCells.source K 5 ell B.L)
      (CWCells.basis K 5 ell B.L) (fun i x ↦ pull i (fine x))
      (fun (_ : Fin 1) ↦ allowed 5 ell B.L (Equiv.refl _) B.cell B.shape B.mu)
    · intro j i x hx
      apply B.inside i (fun j ↦ fine x (Fin.cast B.length.symm j))
      rw [scalarBundle10_split_cast]
      exact hx
    · intro x js _ _
      exact ⟨0, funext (fun i ↦ Fin.eq_zero (js i))⟩
  have hp : tensor K pull = tensor K P := scalarBundle10_tensor_cast B.length P
  rw [hp] at hmono
  exact hboundary.trans hmono

end

section
-- Theorems.Thm_mme_flatteningRank_MMObj_ab


/-!
# `a*b ≤ flatteningRank σ_0 (MMObj K a b c)` for `c ≥ 1`

The mode-0 flattening rank of the matrix-multiplication tensor `MM(a,b,c)` is at least
`a*b` whenever `c ≥ 1`. Direct-rank-functional proof: we construct `a*b` linearly
independent vectors in the range of the flattening map.

For each (i₀, j₀) ∈ Fin a × Fin b, take the left-block basis dual at `(i₀, j₀)`. Its
image under the flattening map equals `∑_k R_{i₀,j₀,k}`, where R is the right-block
pure tensor with mode-1 entry `e_{(j₀,k)}` and mode-2 entry `e_{(k,i₀)}`. These images
for different (i₀, j₀) have disjoint basis support (mode 1 starts with j₀, mode 2 ends
with i₀), so they're linearly independent when c ≥ 1. -/

set_option maxHeartbeats 1600000

universe u

open PiTensorProduct TensorProduct BigOperators Module

namespace MMEFlatteningRankMMObjAbSol

open MME

variable {K : Type u} [Field K]

section MMObj_ab

/-- The mode-0 split `{0} | {1,2}` of `Fin 3`. -/
private noncomputable abbrev scalarBundle11_σ0 : Split (Fin 3) := diagSplit (d := 3) (by norm_num)

/-- `scalarBundle11_σ0.S = {0}` has a unique element. -/
private instance scalarBundle11_σ0_S_subsingleton : Subsingleton (scalarBundle11_σ0 : Split (Fin 3)).S := by
  refine ⟨fun x y => ?_⟩
  ext
  have hx : (x : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3)) := x.2
  have hy : (y : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3)) := y.2
  rw [Finset.mem_singleton] at hx hy
  rw [hx, hy]

/-- The element `0 : Fin 3` packaged as a member of `scalarBundle11_σ0.S = {0}`. -/
private def scalarBundle11_sZero : (scalarBundle11_σ0 : Split (Fin 3)).S :=
  ⟨(0 : Fin 3), by simp [scalarBundle11_σ0, diagSplit]⟩

/-- `scalarBundle11_σ0.S` is nonempty. -/
private instance scalarBundle11_σ0_S_nonempty : Nonempty (scalarBundle11_σ0 : Split (Fin 3)).S := ⟨scalarBundle11_sZero⟩

/-- Decidable equality on `scalarBundle11_σ0.S`. -/
private instance scalarBundle11_σ0_S_decEq : DecidableEq (scalarBundle11_σ0 : Split (Fin 3)).S := by
  intro x y
  exact Decidable.isTrue (Subsingleton.elim _ _)

/-- The element `0 : Fin 3` is in `scalarBundle11_σ0.S`. -/
private lemma scalarBundle11_sZero_val : (scalarBundle11_sZero : (scalarBundle11_σ0 : Split (Fin 3)).S).val = 0 := rfl

/-- For any `s ∈ Sc scalarBundle11_σ0`, `s.val ≠ 0`. -/
private lemma scalarBundle11_sc_ne_zero (s : Sc (scalarBundle11_σ0 : Split (Fin 3))) : (s.val : Fin 3) ≠ 0 := by
  intro h
  have hm : (s.val : Fin 3) ∈ (scalarBundle11_σ0 : Split (Fin 3)).Sᶜ := s.2
  rw [h] at hm
  have h0 : (0 : Fin 3) ∈ (scalarBundle11_σ0 : Split (Fin 3)).S := by
    show (0 : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3))
    rw [Finset.mem_singleton]
  exact Finset.mem_compl.mp hm h0

/-- The basis-index type for each mode of `MMObj K a b c`, uniformly on `Fin 3`. -/
private def scalarBundle11_MMIdx (a b c : ℕ) : Fin 3 → Type
  | ⟨0, _⟩ => Fin a × Fin b
  | ⟨1, _⟩ => Fin b × Fin c
  | ⟨2, _⟩ => Fin c × Fin a
  | ⟨_+3, h⟩ => absurd h (by omega)

private instance scalarBundle11_MMIdx_fintype (a b c : ℕ) (i : Fin 3) : Fintype (scalarBundle11_MMIdx a b c i) := by
  match i with
  | ⟨0, _⟩ => exact inferInstanceAs (Fintype (Fin a × Fin b))
  | ⟨1, _⟩ => exact inferInstanceAs (Fintype (Fin b × Fin c))
  | ⟨2, _⟩ => exact inferInstanceAs (Fintype (Fin c × Fin a))

private instance scalarBundle11_MMIdx_decEq (a b c : ℕ) (i : Fin 3) : DecidableEq (scalarBundle11_MMIdx a b c i) := by
  match i with
  | ⟨0, _⟩ => exact inferInstanceAs (DecidableEq (Fin a × Fin b))
  | ⟨1, _⟩ => exact inferInstanceAs (DecidableEq (Fin b × Fin c))
  | ⟨2, _⟩ => exact inferInstanceAs (DecidableEq (Fin c × Fin a))

/-- The left-block family is constant `Fin a × Fin b → K`. -/
private lemma scalarBundle11_left_family_eq (a b c : ℕ) :
    (fun i : (scalarBundle11_σ0 : Split (Fin 3)).S => (MMObj K a b c).V i.val) =
    (fun _ : (scalarBundle11_σ0 : Split (Fin 3)).S => (Fin a × Fin b → K)) := by
  funext x
  have hx0 : (x : Fin 3) = 0 := Finset.mem_singleton.mp x.2
  rw [hx0]; rfl

/-- The right-block family equals `fun i => scalarBundle11_MMIdx a b c i.val → K`. -/
private lemma scalarBundle11_right_family_eq (a b c : ℕ) :
    (fun i : Sc (scalarBundle11_σ0 : Split (Fin 3)) => (MMObj K a b c).V i.val) =
    (fun i : Sc (scalarBundle11_σ0 : Split (Fin 3)) => (scalarBundle11_MMIdx a b c i.val → K)) := by
  funext x
  match h : (x.val : Fin 3) with
  | ⟨0, _⟩ => exact absurd h (scalarBundle11_sc_ne_zero x)
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- Per-mode basis (matching `MMSpace`). -/
private noncomputable def scalarBundle11_MMBasis (K : Type u) [Field K] (a b c : ℕ) :
    ∀ i : Fin 3, Basis (scalarBundle11_MMIdx a b c i) K (MMSpace K a b c i) := by
  intro i
  match i with
  | ⟨0, _⟩ => exact Pi.basisFun K (Fin a × Fin b)
  | ⟨1, _⟩ => exact Pi.basisFun K (Fin b × Fin c)
  | ⟨2, _⟩ => exact Pi.basisFun K (Fin c × Fin a)

/-- Left-block basis: indexed by `scalarBundle11_σ0.S → Fin a × Fin b`. -/
private noncomputable def scalarBundle11_bL (a b c : ℕ) :
    Basis ((scalarBundle11_σ0 : Split (Fin 3)).S → Fin a × Fin b) K
      (PiTensorProduct K (fun i : (scalarBundle11_σ0 : Split (Fin 3)).S =>
        (MMObj K a b c).V i.val)) :=
  Basis.piTensorProduct (fun i : (scalarBundle11_σ0 : Split (Fin 3)).S =>
    (show (scalarBundle11_MMIdx a b c i.val) = (Fin a × Fin b) by
      have hx0 : (i : Fin 3) = 0 := Finset.mem_singleton.mp i.2
      rw [hx0]; rfl) ▸ scalarBundle11_MMBasis K a b c i.val)

/-- Right-block basis: indexed by `∀ s : Sc scalarBundle11_σ0, scalarBundle11_MMIdx a b c s.val`. -/
private noncomputable def scalarBundle11_bR (a b c : ℕ) :
    Basis (∀ s : Sc (scalarBundle11_σ0 : Split (Fin 3)), scalarBundle11_MMIdx a b c s.val) K
      (PiTensorProduct K (fun i : Sc (scalarBundle11_σ0 : Split (Fin 3)) =>
        (MMObj K a b c).V i.val)) :=
  Basis.piTensorProduct (fun s : Sc (scalarBundle11_σ0 : Split (Fin 3)) => scalarBundle11_MMBasis K a b c s.val)

/-- The right-block basis index `g_{i₀,j₀,k}` corresponding to the pure tensor with
mode-1 entry `e_{(j₀,k)}` and mode-2 entry `e_{(k,i₀)}`. -/
private noncomputable def scalarBundle11_gR (a b c : ℕ)
    (i₀ : Fin a) (j₀ : Fin b) (k : Fin c) :
    ∀ s : Sc (scalarBundle11_σ0 : Split (Fin 3)), scalarBundle11_MMIdx a b c s.val := fun s =>
  match h : (s.val : Fin 3) with
  | ⟨0, _⟩ => absurd h (scalarBundle11_sc_ne_zero s)
  | ⟨1, _⟩ => (j₀, k)
  | ⟨2, _⟩ => (k, i₀)

/-- The candidate vector `scalarBundle11_vec (i₀, j₀)` in `V_right`: sum of right-block basis tensors
indexed by `scalarBundle11_gR i₀ j₀ k` for `k ∈ Fin c`. -/
private noncomputable def scalarBundle11_vec (a b c : ℕ) (ij : Fin a × Fin b) :
    PiTensorProduct K (fun i : Sc (scalarBundle11_σ0 : Split (Fin 3)) => (MMObj K a b c).V i.val) :=
  ∑ k : Fin c, scalarBundle11_bR a b c (scalarBundle11_gR a b c ij.1 ij.2 k)

/-- A concrete element of `Sc scalarBundle11_σ0` with value `1`. -/
private noncomputable def scalarBundle11_sOne : Sc (scalarBundle11_σ0 : Split (Fin 3)) :=
  ⟨(1 : Fin 3), by
    show (1 : Fin 3) ∈ (scalarBundle11_σ0 : Split (Fin 3)).Sᶜ
    rw [Finset.mem_compl]
    intro h
    have : (1 : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3)) := h
    have h01 : (1 : Fin 3) = 0 := Finset.mem_singleton.mp this
    exact absurd h01 (by decide)⟩

/-- A concrete element of `Sc scalarBundle11_σ0` with value `2`. -/
private noncomputable def scalarBundle11_sTwo : Sc (scalarBundle11_σ0 : Split (Fin 3)) :=
  ⟨(2 : Fin 3), by
    show (2 : Fin 3) ∈ (scalarBundle11_σ0 : Split (Fin 3)).Sᶜ
    rw [Finset.mem_compl]
    intro h
    have : (2 : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3)) := h
    have h02 : (2 : Fin 3) = 0 := Finset.mem_singleton.mp this
    exact absurd h02 (by decide)⟩

private lemma scalarBundle11_sOne_val : (scalarBundle11_sOne : Sc (scalarBundle11_σ0 : Split (Fin 3))).val = (1 : Fin 3) := rfl
private lemma scalarBundle11_sTwo_val : (scalarBundle11_sTwo : Sc (scalarBundle11_σ0 : Split (Fin 3))).val = (2 : Fin 3) := rfl

/-- `scalarBundle11_gR ij.1 ij.2 k` evaluated at `scalarBundle11_sOne` (mode-1 slot) gives `(ij.2, k)`. -/
private lemma scalarBundle11_gR_at_sOne (a b c : ℕ) (i₀ : Fin a) (j₀ : Fin b) (k : Fin c) :
    (scalarBundle11_gR a b c i₀ j₀ k scalarBundle11_sOne : scalarBundle11_MMIdx a b c (scalarBundle11_sOne : Sc (scalarBundle11_σ0 : Split (Fin 3))).val) = (j₀, k) := by
  unfold scalarBundle11_gR
  rfl

/-- `scalarBundle11_gR ij.1 ij.2 k` evaluated at `scalarBundle11_sTwo` (mode-2 slot) gives `(k, ij.1)`. -/
private lemma scalarBundle11_gR_at_sTwo (a b c : ℕ) (i₀ : Fin a) (j₀ : Fin b) (k : Fin c) :
    (scalarBundle11_gR a b c i₀ j₀ k scalarBundle11_sTwo : scalarBundle11_MMIdx a b c (scalarBundle11_sTwo : Sc (scalarBundle11_σ0 : Split (Fin 3))).val) = (k, i₀) := by
  unfold scalarBundle11_gR
  rfl

/-- The combined index `(ij, k) ↦ scalarBundle11_gR ij.1 ij.2 k` is injective. -/
private lemma scalarBundle11_gR_injective (a b c : ℕ) :
    Function.Injective (fun (p : (Fin a × Fin b) × Fin c) =>
      scalarBundle11_gR a b c p.1.1 p.1.2 p.2) := by
  rintro ⟨⟨i₀, j₀⟩, k⟩ ⟨⟨i₀', j₀'⟩, k'⟩ h
  simp only at h
  -- evaluate at scalarBundle11_sOne to get (j₀, k) = (j₀', k')
  have h1 : scalarBundle11_gR a b c i₀ j₀ k scalarBundle11_sOne = scalarBundle11_gR a b c i₀' j₀' k' scalarBundle11_sOne := by
    rw [h]
  rw [scalarBundle11_gR_at_sOne, scalarBundle11_gR_at_sOne] at h1
  -- evaluate at scalarBundle11_sTwo to get (k, i₀) = (k', i₀')
  have h2 : scalarBundle11_gR a b c i₀ j₀ k scalarBundle11_sTwo = scalarBundle11_gR a b c i₀' j₀' k' scalarBundle11_sTwo := by
    rw [h]
  rw [scalarBundle11_gR_at_sTwo, scalarBundle11_gR_at_sTwo] at h2
  obtain ⟨hj, hk⟩ := Prod.mk.inj h1
  obtain ⟨hk', hi⟩ := Prod.mk.inj h2
  simp [hi, hj, hk]

/-- For different `ij ≠ ij'`, the images `{scalarBundle11_gR ij.1 ij.2 k | k}` and
`{scalarBundle11_gR ij'.1 ij'.2 k | k}` are disjoint. -/
private lemma scalarBundle11_gR_disjoint (a b c : ℕ) {ij ij' : Fin a × Fin b} (hne : ij ≠ ij')
    (k k' : Fin c) :
    scalarBundle11_gR a b c ij.1 ij.2 k ≠ scalarBundle11_gR a b c ij'.1 ij'.2 k' := by
  intro h
  apply hne
  -- evaluate at scalarBundle11_sOne for j-component
  have h1 : scalarBundle11_gR a b c ij.1 ij.2 k scalarBundle11_sOne = scalarBundle11_gR a b c ij'.1 ij'.2 k' scalarBundle11_sOne := by rw [h]
  rw [scalarBundle11_gR_at_sOne, scalarBundle11_gR_at_sOne] at h1
  obtain ⟨hj, _⟩ := Prod.mk.inj h1
  -- evaluate at scalarBundle11_sTwo for i-component
  have h2 : scalarBundle11_gR a b c ij.1 ij.2 k scalarBundle11_sTwo = scalarBundle11_gR a b c ij'.1 ij'.2 k' scalarBundle11_sTwo := by rw [h]
  rw [scalarBundle11_gR_at_sTwo, scalarBundle11_gR_at_sTwo] at h2
  obtain ⟨_, hi⟩ := Prod.mk.inj h2
  exact Prod.ext hi hj

/-- **Linear independence of `scalarBundle11_vec`.** Uses dual functionals:
the basis coord `scalarBundle11_bR.coord (scalarBundle11_gR ij.1 ij.2 ⟨0, hc⟩)` evaluates to 1 on `scalarBundle11_vec ij` and to 0
on `scalarBundle11_vec ij'` for `ij ≠ ij'`. -/
private lemma scalarBundle11_vec_linearIndependent (a b c : ℕ) (hc : 1 ≤ c) :
    LinearIndependent K (scalarBundle11_vec (K := K) a b c) := by
  -- the dual functional family
  let φ : Fin a × Fin b → Dual K
      (PiTensorProduct K (fun i : Sc (scalarBundle11_σ0 : Split (Fin 3)) =>
        (MMObj K a b c).V i.val)) :=
    fun ij => (scalarBundle11_bR a b c).coord (scalarBundle11_gR a b c ij.1 ij.2 ⟨0, hc⟩)
  refine LinearIndependent.of_pairwise_dual_eq_zero_one (v := scalarBundle11_vec a b c) (f := φ) ?_ ?_
  · intro ij ij' hne
    -- φ ij (scalarBundle11_vec ij') = ∑_k scalarBundle11_bR.coord (scalarBundle11_gR ij.1 ij.2 ⟨0,hc⟩) (scalarBundle11_bR (scalarBundle11_gR ij'.1 ij'.2 k))
    -- = ∑_k δ_{scalarBundle11_gR ij'.1 ij'.2 k = scalarBundle11_gR ij.1 ij.2 ⟨0,hc⟩} = 0 (since ij' ≠ ij ⇒ disjoint)
    show φ ij (scalarBundle11_vec a b c ij') = 0
    unfold scalarBundle11_vec
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [Basis.coord_apply, Basis.repr_self_apply]
    rw [if_neg]
    intro h
    exact scalarBundle11_gR_disjoint a b c (Ne.symm hne) k ⟨0, hc⟩ h
  · intro ij
    -- φ ij (scalarBundle11_vec ij) = ∑_k δ_{scalarBundle11_gR ij.1 ij.2 k = scalarBundle11_gR ij.1 ij.2 ⟨0,hc⟩} = 1 (only k=⟨0,hc⟩)
    show φ ij (scalarBundle11_vec a b c ij) = 1
    unfold scalarBundle11_vec
    rw [map_sum]
    rw [Finset.sum_eq_single (⟨0, hc⟩ : Fin c)]
    · rw [Basis.coord_apply, Basis.repr_self_apply, if_pos rfl]
    · intro k _ hk
      rw [Basis.coord_apply, Basis.repr_self_apply, if_neg]
      intro h
      have hinj := scalarBundle11_gR_injective a b c
      have : ((ij, k) : (Fin a × Fin b) × Fin c) = ((ij, ⟨0, hc⟩) : (Fin a × Fin b) × Fin c) := by
        apply hinj
        exact h
      have := (Prod.mk.inj this).2
      exact hk this
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Step 2: Each `scalarBundle11_vec ij` is in the range of the flattening map. -/

/-- The dual functional that "picks out coordinate `ij`" via the singleton
identification of the left block. Concretely: pull back the evaluation-at-`ij`
functional on `Fin a × Fin b → K` through `subsingletonEquiv scalarBundle11_sZero`. -/
private noncomputable def scalarBundle11_dualL (a b c : ℕ) (ij : Fin a × Fin b) :
    Dual K (PiTensorProduct K (fun i : (scalarBundle11_σ0 : Split (Fin 3)).S =>
      (MMObj K a b c).V i.val)) :=
  (LinearMap.proj ij : (Fin a × Fin b → K) →ₗ[K] K).comp
    ((PiTensorProduct.subsingletonEquiv scalarBundle11_sZero).toLinearMap :
      PiTensorProduct K (fun i : (scalarBundle11_σ0 : Split (Fin 3)).S =>
        (MMObj K a b c).V i.val) →ₗ[K] (Fin a × Fin b → K))

/-- `scalarBundle11_dualL ij` applied to a pure tensor `tprod K v` evaluates `v 0` at `ij`. -/
private lemma scalarBundle11_dualL_tprod (a b c : ℕ) (ij : Fin a × Fin b)
    (v : ∀ s : (scalarBundle11_σ0 : Split (Fin 3)).S, (MMObj K a b c).V s.val) :
    scalarBundle11_dualL a b c ij (tprod K v) = (v scalarBundle11_sZero : Fin a × Fin b → K) ij := by
  unfold scalarBundle11_dualL
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  -- Use subsingletonEquiv_apply_tprod directly
  have h : (PiTensorProduct.subsingletonEquiv scalarBundle11_sZero : PiTensorProduct K
      (fun i : (scalarBundle11_σ0 : Split (Fin 3)).S => (MMObj K a b c).V i.val) ≃ₗ[K]
      (MMObj K a b c).V (scalarBundle11_sZero : (scalarBundle11_σ0 : Split (Fin 3)).S).val) (tprod K v) =
      v scalarBundle11_sZero :=
    PiTensorProduct.subsingletonEquiv_apply_tprod _ _
  -- coerce via toLinearMap
  show (PiTensorProduct.subsingletonEquiv scalarBundle11_sZero) (tprod K v) ij = v scalarBundle11_sZero ij
  rw [h]

/-- The mode-wise data function for the (i, j, k) term of `MMTensor K a b c`. -/
private noncomputable def scalarBundle11_modeData (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    ∀ s : Fin 3, MMSpace K a b c s := fun s =>
  match s with
  | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin a × Fin b → K)
  | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin b × Fin c → K)
  | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin c × Fin a → K)

/-- `MMTensor K a b c` written as a triple sum using `scalarBundle11_modeData`. -/
private lemma scalarBundle11_MMTensor_eq_sum (a b c : ℕ) :
    MMTensor K a b c = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
      tprod K (scalarBundle11_modeData (K := K) a b c i j k) := by
  rfl

/-- The "left" tensor of the (i, j, k) term after `splitTensorEquiv scalarBundle11_σ0`. -/
private noncomputable def scalarBundle11_Lterm (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct K (fun s : (scalarBundle11_σ0 : Split (Fin 3)).S => (MMObj K a b c).V s.val) :=
  tprod K (fun s : (scalarBundle11_σ0 : Split (Fin 3)).S => scalarBundle11_modeData a b c i j k s.val)

/-- The "right" tensor of the (i, j, k) term after `splitTensorEquiv scalarBundle11_σ0`. -/
private noncomputable def scalarBundle11_Rterm (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct K (fun s : Sc (scalarBundle11_σ0 : Split (Fin 3)) => (MMObj K a b c).V s.val) :=
  tprod K (fun s : Sc (scalarBundle11_σ0 : Split (Fin 3)) => scalarBundle11_modeData a b c i j k s.val)

/-- `splitTensorEquiv` of one pure term decomposes into `scalarBundle11_Lterm ⊗ₜ scalarBundle11_Rterm`. -/
private lemma scalarBundle11_splitTensorEquiv_term (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    splitTensorEquiv scalarBundle11_σ0 (tprod K (scalarBundle11_modeData (K := K) a b c i j k))
      = scalarBundle11_Lterm a b c i j k ⊗ₜ[K] scalarBundle11_Rterm a b c i j k :=
  splitTensorEquiv_tprod _ _

/-- The `scalarBundle11_dualL ij` value on `scalarBundle11_Lterm i j k` is `δ_{(i,j) = ij}`. -/
private lemma scalarBundle11_dualL_Lterm (a b c : ℕ) (ij : Fin a × Fin b)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    scalarBundle11_dualL a b c ij (scalarBundle11_Lterm a b c i j k) = if (i, j) = ij then (1 : K) else 0 := by
  unfold scalarBundle11_Lterm
  rw [scalarBundle11_dualL_tprod]
  -- scalarBundle11_modeData i j k (scalarBundle11_sZero : scalarBundle11_σ0.S).val = scalarBundle11_modeData i j k 0 = Pi.single (i, j) 1
  show (scalarBundle11_modeData (K := K) a b c i j k (scalarBundle11_sZero : (scalarBundle11_σ0 : Split (Fin 3)).S).val :
    Fin a × Fin b → K) ij = if (i, j) = ij then (1 : K) else 0
  -- by scalarBundle11_sZero_val: scalarBundle11_sZero.val = 0, so scalarBundle11_modeData ... 0 = Pi.single (i,j) 1
  rw [show scalarBundle11_modeData (K := K) a b c i j k (scalarBundle11_sZero : (scalarBundle11_σ0 : Split (Fin 3)).S).val =
      (Pi.single (i, j) 1 : Fin a × Fin b → K) from rfl]
  rw [Pi.single_apply]
  by_cases h : ij = (i, j)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- `scalarBundle11_Rterm i j k = scalarBundle11_bR (scalarBundle11_gR i j k)`. -/
private lemma scalarBundle11_Rterm_eq_bR (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    (scalarBundle11_Rterm (K := K) a b c i j k) = scalarBundle11_bR (K := K) a b c (scalarBundle11_gR a b c i j k) := by
  unfold scalarBundle11_Rterm scalarBundle11_bR
  rw [Basis.piTensorProduct_apply]
  congr 1
  funext s
  show scalarBundle11_modeData (K := K) a b c i j k s.val = scalarBundle11_MMBasis K a b c s.val (scalarBundle11_gR a b c i j k s)
  -- Case analysis on s.val
  rcases s with ⟨sv, hsv⟩
  have hne : sv ≠ 0 := scalarBundle11_sc_ne_zero ⟨sv, hsv⟩
  match sv, hne with
  | ⟨1, hsv1⟩, _ =>
    show (Pi.single (j, k) 1 : Fin b × Fin c → K) =
      scalarBundle11_MMBasis K a b c (⟨1, hsv1⟩ : Fin 3) (scalarBundle11_gR a b c i j k ⟨⟨1, hsv1⟩, hsv⟩)
    show (Pi.single (j, k) 1 : Fin b × Fin c → K) =
      Pi.basisFun K (Fin b × Fin c) (scalarBundle11_gR a b c i j k ⟨⟨1, hsv1⟩, hsv⟩)
    rw [Pi.basisFun_apply]
    rfl
  | ⟨2, hsv2⟩, _ =>
    show (Pi.single (k, i) 1 : Fin c × Fin a → K) =
      scalarBundle11_MMBasis K a b c (⟨2, hsv2⟩ : Fin 3) (scalarBundle11_gR a b c i j k ⟨⟨2, hsv2⟩, hsv⟩)
    show (Pi.single (k, i) 1 : Fin c × Fin a → K) =
      Pi.basisFun K (Fin c × Fin a) (scalarBundle11_gR a b c i j k ⟨⟨2, hsv2⟩, hsv⟩)
    rw [Pi.basisFun_apply]
    rfl
  | ⟨0, _⟩, h => exact absurd rfl h

/-- The key formula expressing `flatteningMap scalarBundle11_σ0 (MMObj K a b c) (scalarBundle11_dualL ij)` as
`∑_{i,j,k} δ_{(i,j)=ij} • scalarBundle11_bR (scalarBundle11_gR i j k) = scalarBundle11_vec ij`. -/
private lemma scalarBundle11_flatteningMap_MMObj_dualL_eq_vec (a b c : ℕ) (ij : Fin a × Fin b) :
    flatteningMap scalarBundle11_σ0 (MMObj K a b c) (scalarBundle11_dualL a b c ij) = scalarBundle11_vec a b c ij := by
  -- Unfold flatteningMap.
  unfold flatteningMap
  -- Expand X.t.
  show tensorToDualHom K _ _ (splitTensorEquiv scalarBundle11_σ0 (MMTensor K a b c)) (scalarBundle11_dualL a b c ij) =
    scalarBundle11_vec a b c ij
  rw [scalarBundle11_MMTensor_eq_sum]
  -- distribute splitTensorEquiv through the triple sum
  rw [show splitTensorEquiv scalarBundle11_σ0 (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        tprod K (scalarBundle11_modeData (K := K) a b c i j k))
      = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        scalarBundle11_Lterm a b c i j k ⊗ₜ[K] scalarBundle11_Rterm a b c i j k from ?_]
  swap
  · simp only [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact scalarBundle11_splitTensorEquiv_term a b c i j k
  -- distribute tensorToDualHom through the sums.
  have hreduce : ((tensorToDualHom K
      (PiTensorProduct K (fun s : (scalarBundle11_σ0 : Split (Fin 3)).S => (MMObj K a b c).V s.val))
      (PiTensorProduct K (fun s : Sc (scalarBundle11_σ0 : Split (Fin 3)) => (MMObj K a b c).V s.val)))
      (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        scalarBundle11_Lterm a b c i j k ⊗ₜ[K] scalarBundle11_Rterm a b c i j k)) (scalarBundle11_dualL a b c ij) =
      ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        scalarBundle11_dualL (K := K) a b c ij (scalarBundle11_Lterm a b c i j k) • scalarBundle11_Rterm (K := K) a b c i j k := by
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [tensorToDualHom_tmul]
  change ((tensorToDualHom K
      (PiTensorProduct K (fun s : (scalarBundle11_σ0 : Split (Fin 3)).S => (MMObj K a b c).V s.val))
      (PiTensorProduct K (fun s : Sc (scalarBundle11_σ0 : Split (Fin 3)) => (MMObj K a b c).V s.val)))
      (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        scalarBundle11_Lterm a b c i j k ⊗ₜ[K] scalarBundle11_Rterm a b c i j k)) (scalarBundle11_dualL a b c ij) = _
  rw [hreduce]
  -- now use scalarBundle11_dualL_Lterm to replace the dual value with δ
  simp_rw [scalarBundle11_dualL_Lterm]
  -- Replace scalarBundle11_Rterm with scalarBundle11_bR (scalarBundle11_gR i j k).
  simp_rw [scalarBundle11_Rterm_eq_bR]
  -- The goal now is:
  -- ∑ i, ∑ j, ∑ k, (if (i,j) = ij then 1 else 0) • scalarBundle11_bR (scalarBundle11_gR i j k) = scalarBundle11_vec ij
  -- scalarBundle11_vec ij = ∑_k scalarBundle11_bR (scalarBundle11_gR ij.1 ij.2 k).
  -- For each (i, j), the inner ∑_k is either 0 (if (i,j) ≠ ij) or ∑_k scalarBundle11_bR (scalarBundle11_gR i j k).
  -- Strategy: swap sums, then collapse i, j.
  unfold scalarBundle11_vec
  -- Goal: ∑ i, ∑ j, ∑ k, (if (i,j) = ij then 1 else 0) • scalarBundle11_bR (scalarBundle11_gR i j k) =
  --       ∑ k, scalarBundle11_bR (scalarBundle11_gR ij.1 ij.2 k)
  -- Collapse: for fixed k, ∑_{i,j} δ_{(i,j)=ij} scalarBundle11_bR (scalarBundle11_gR i j k) = scalarBundle11_bR (scalarBundle11_gR ij.1 ij.2 k).
  -- Then ∑_k ∑_{i,j} ... = ∑_k scalarBundle11_bR (...).
  -- Step: pull out the inner ∑_k, since the if condition doesn't depend on k.
  -- ∑_i ∑_j ∑_k (δ • scalarBundle11_bR) = ∑_i ∑_j (δ • ∑_k scalarBundle11_bR) = ∑_i ∑_j δ • (∑_k scalarBundle11_bR (scalarBundle11_gR i j k))
  -- Wait — the δ is independent of k, so we can move it outside ∑_k:
  -- ∑_i ∑_j ∑_k (δ • scalarBundle11_bR (scalarBundle11_gR i j k)) = ∑_i ∑_j (δ • ∑_k scalarBundle11_bR (scalarBundle11_gR i j k))
  simp_rw [← Finset.smul_sum]
  -- Goal: ∑ i, ∑ j, (if (i,j) = ij then 1 else 0) • ∑ k, scalarBundle11_bR (scalarBundle11_gR i j k) = ∑ k, scalarBundle11_bR (scalarBundle11_gR ij.1 ij.2 k)
  -- Now collapse ∑_i ∑_j δ • f(i,j) by Finset.sum_eq_single
  rw [Finset.sum_eq_single ij.1]
  · rw [Finset.sum_eq_single ij.2]
    · rw [if_pos rfl, one_smul]
    · intro j _ hj
      rw [if_neg, zero_smul]
      intro h
      apply hj
      exact (Prod.mk.inj h).2
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    rw [Finset.sum_eq_zero]
    intro j _
    rw [if_neg, zero_smul]
    intro h
    apply hi
    exact (Prod.mk.inj h).1
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`scalarBundle11_vec ij ∈ range (flatteningMap scalarBundle11_σ0 (MMObj K a b c))`.** -/
private lemma scalarBundle11_vec_mem_range (a b c : ℕ) (ij : Fin a × Fin b) :
    scalarBundle11_vec a b c ij ∈ LinearMap.range (flatteningMap scalarBundle11_σ0 (MMObj K a b c)) := by
  exact ⟨scalarBundle11_dualL a b c ij, scalarBundle11_flatteningMap_MMObj_dualL_eq_vec a b c ij⟩

end MMObj_ab

end MMEFlatteningRankMMObjAbSol

/-! ### Main result (top-level for platform upload) -/

open MMEFlatteningRankMMObjAbSol MME

/-- The mode-0 flattening rank of `MMObj K a b c` is at least `a * b` when `c ≥ 1`.

Proof: we construct `a * b` linearly independent vectors `scalarBundle11_vec ij` in the range of the
flattening map. Each `scalarBundle11_vec ij = ∑_k scalarBundle11_bR (scalarBundle11_gR ij.1 ij.2 k)` is a sum of right-block basis
tensors, and the index map `(ij, k) ↦ scalarBundle11_gR ij.1 ij.2 k` is injective; combined with `c ≥ 1`,
this yields linear independence. The witness dual is `scalarBundle11_bL.coord (fun _ => ij)`. -/
theorem mme_flatteningRank_MMObj_ab {K : Type u} [Field K] (a b c : ℕ) (hc : 1 ≤ c) :
    a * b ≤ MME.flatteningRank (MME.diagSplit (d := 3) (by norm_num)) (MME.MMObj K a b c) := by
  -- The candidate vectors are `scalarBundle11_vec ij` for `ij ∈ Fin a × Fin b`.
  -- They are LI and contained in the range, so we get a*b ≤ finrank range.
  unfold flatteningRank
  -- Express scalarBundle11_vec via the range submodule.
  set V_right := PiTensorProduct K (fun i : Sc (scalarBundle11_σ0 : Split (Fin 3)) =>
    (MMObj K a b c).V i.val) with hVright
  haveI : FiniteDimensional K V_right :=
    Module.Finite.of_basis (scalarBundle11_bR a b c)
  set rangeFM := LinearMap.range (flatteningMap scalarBundle11_σ0 (MMObj K a b c)) with hrangeFM
  -- pull back scalarBundle11_vec into rangeFM
  let vecInRange : Fin a × Fin b → rangeFM := fun ij =>
    ⟨scalarBundle11_vec a b c ij, scalarBundle11_vec_mem_range a b c ij⟩
  -- LI of vecInRange follows from LI of scalarBundle11_vec.
  have hLI : LinearIndependent K vecInRange := by
    have hLI₀ : LinearIndependent K (scalarBundle11_vec (K := K) a b c) :=
      scalarBundle11_vec_linearIndependent a b c hc
    -- pulling back LI through subtype inclusion preserves LI
    exact hLI₀.of_comp rangeFM.subtype
  -- Apply: |Fin a × Fin b| ≤ finrank rangeFM.
  have hcard : Fintype.card (Fin a × Fin b) = a * b := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  -- finite-dim version
  have := hLI.fintype_card_le_finrank (R := K) (M := rangeFM)
  rw [hcard] at this
  exact this

end

section
-- Theorems.Thm_mme_flatteningRank_MMObj_bc
namespace MME

/-- The singleton split `S = {1}` of `Fin 3`. -/
noncomputable def split1 : Split (Fin 3) where
  S := {(1 : Fin 3)}
  hS := Finset.singleton_nonempty _
  hSc := by
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    intro h
    have hcard : ({(1 : Fin 3)}ᶜ : Finset (Fin 3)).card = 0 := by rw [h]; rfl
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin] at hcard
    omega

end MME

/-!
# `b*c ≤ flatteningRank σ_1 (MMObj K a b c)` for `a ≥ 1`

Mode-1 cyclic analogue of `Sol_mme_flatteningRank_MMObj_ab`. We construct `b*c` linearly
independent vectors in the range of the mode-1 flattening map.

For each (j₀, k₀) ∈ Fin b × Fin c, take the left-block basis dual at `(j₀, k₀)`. Its
image under the flattening map equals `∑_i R_{i,j₀,k₀}`, where R is the right-block
pure tensor with mode-0 entry `e_{(i,j₀)}` and mode-2 entry `e_{(k₀,i)}`. These images
for different (j₀, k₀) have disjoint basis support, so they're linearly independent
when a ≥ 1. -/

set_option maxHeartbeats 1600000

universe u

open PiTensorProduct TensorProduct BigOperators Module

namespace MMEFlatteningRankMMObjBcSol

open MME

variable {K : Type u} [Field K]

section MMObj_bc

/-- Alias for `split1`. -/
private noncomputable abbrev scalarBundle12_σ1 : Split (Fin 3) := split1

/-- `scalarBundle12_σ1.S = {1}` has a unique element. -/
private instance scalarBundle12_σ1_S_subsingleton : Subsingleton (scalarBundle12_σ1 : Split (Fin 3)).S := by
  refine ⟨fun x y => ?_⟩
  ext
  have hx : (x : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) := x.2
  have hy : (y : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) := y.2
  rw [Finset.mem_singleton] at hx hy
  rw [hx, hy]

/-- The element `1 : Fin 3` packaged as a member of `scalarBundle12_σ1.S = {1}`. -/
private def scalarBundle12_sOneL : (scalarBundle12_σ1 : Split (Fin 3)).S :=
  ⟨(1 : Fin 3), by simp [scalarBundle12_σ1, split1]⟩

/-- `scalarBundle12_σ1.S` is nonempty. -/
private instance scalarBundle12_σ1_S_nonempty : Nonempty (scalarBundle12_σ1 : Split (Fin 3)).S := ⟨scalarBundle12_sOneL⟩

/-- Decidable equality on `scalarBundle12_σ1.S`. -/
private instance scalarBundle12_σ1_S_decEq : DecidableEq (scalarBundle12_σ1 : Split (Fin 3)).S := by
  intro x y
  exact Decidable.isTrue (Subsingleton.elim _ _)

/-- The element `1 : Fin 3` is in `scalarBundle12_σ1.S`. -/
private lemma scalarBundle12_sOneL_val : (scalarBundle12_sOneL : (scalarBundle12_σ1 : Split (Fin 3)).S).val = 1 := rfl

/-- For any `s ∈ Sc scalarBundle12_σ1`, `s.val ≠ 1`. -/
private lemma scalarBundle12_sc_ne_one (s : Sc (scalarBundle12_σ1 : Split (Fin 3))) : (s.val : Fin 3) ≠ 1 := by
  intro h
  have hm : (s.val : Fin 3) ∈ (scalarBundle12_σ1 : Split (Fin 3)).Sᶜ := s.2
  rw [h] at hm
  have h1 : (1 : Fin 3) ∈ (scalarBundle12_σ1 : Split (Fin 3)).S := by
    show (1 : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3))
    rw [Finset.mem_singleton]
  exact Finset.mem_compl.mp hm h1

/-- The basis-index type for each mode of `MMObj K a b c`, uniformly on `Fin 3`. -/
private def scalarBundle12_MMIdx (a b c : ℕ) : Fin 3 → Type
  | ⟨0, _⟩ => Fin a × Fin b
  | ⟨1, _⟩ => Fin b × Fin c
  | ⟨2, _⟩ => Fin c × Fin a
  | ⟨_+3, h⟩ => absurd h (by omega)

private instance scalarBundle12_MMIdx_fintype (a b c : ℕ) (i : Fin 3) : Fintype (scalarBundle12_MMIdx a b c i) := by
  match i with
  | ⟨0, _⟩ => exact inferInstanceAs (Fintype (Fin a × Fin b))
  | ⟨1, _⟩ => exact inferInstanceAs (Fintype (Fin b × Fin c))
  | ⟨2, _⟩ => exact inferInstanceAs (Fintype (Fin c × Fin a))

private instance scalarBundle12_MMIdx_decEq (a b c : ℕ) (i : Fin 3) : DecidableEq (scalarBundle12_MMIdx a b c i) := by
  match i with
  | ⟨0, _⟩ => exact inferInstanceAs (DecidableEq (Fin a × Fin b))
  | ⟨1, _⟩ => exact inferInstanceAs (DecidableEq (Fin b × Fin c))
  | ⟨2, _⟩ => exact inferInstanceAs (DecidableEq (Fin c × Fin a))

/-- Per-mode basis (matching `MMSpace`). -/
private noncomputable def scalarBundle12_MMBasis (K : Type u) [Field K] (a b c : ℕ) :
    ∀ i : Fin 3, Basis (scalarBundle12_MMIdx a b c i) K (MMSpace K a b c i) := by
  intro i
  match i with
  | ⟨0, _⟩ => exact Pi.basisFun K (Fin a × Fin b)
  | ⟨1, _⟩ => exact Pi.basisFun K (Fin b × Fin c)
  | ⟨2, _⟩ => exact Pi.basisFun K (Fin c × Fin a)

/-- Left-block basis: indexed by `scalarBundle12_σ1.S → Fin b × Fin c`. -/
private noncomputable def scalarBundle12_bL (a b c : ℕ) :
    Basis ((scalarBundle12_σ1 : Split (Fin 3)).S → Fin b × Fin c) K
      (PiTensorProduct K (fun i : (scalarBundle12_σ1 : Split (Fin 3)).S =>
        (MMObj K a b c).V i.val)) :=
  Basis.piTensorProduct (fun i : (scalarBundle12_σ1 : Split (Fin 3)).S =>
    (show (scalarBundle12_MMIdx a b c i.val) = (Fin b × Fin c) by
      have hx1 : (i : Fin 3) = 1 := Finset.mem_singleton.mp i.2
      rw [hx1]; rfl) ▸ scalarBundle12_MMBasis K a b c i.val)

/-- Right-block basis: indexed by `∀ s : Sc scalarBundle12_σ1, scalarBundle12_MMIdx a b c s.val`. -/
private noncomputable def scalarBundle12_bR (a b c : ℕ) :
    Basis (∀ s : Sc (scalarBundle12_σ1 : Split (Fin 3)), scalarBundle12_MMIdx a b c s.val) K
      (PiTensorProduct K (fun i : Sc (scalarBundle12_σ1 : Split (Fin 3)) =>
        (MMObj K a b c).V i.val)) :=
  Basis.piTensorProduct (fun s : Sc (scalarBundle12_σ1 : Split (Fin 3)) => scalarBundle12_MMBasis K a b c s.val)

/-- The right-block basis index `g_{j₀,k₀,i}` corresponding to the pure tensor with
mode-0 entry `e_{(i,j₀)}` and mode-2 entry `e_{(k₀,i)}`. -/
private noncomputable def scalarBundle12_gR (a b c : ℕ)
    (j₀ : Fin b) (k₀ : Fin c) (i : Fin a) :
    ∀ s : Sc (scalarBundle12_σ1 : Split (Fin 3)), scalarBundle12_MMIdx a b c s.val := fun s =>
  match h : (s.val : Fin 3) with
  | ⟨0, _⟩ => (i, j₀)
  | ⟨1, _⟩ => absurd h (scalarBundle12_sc_ne_one s)
  | ⟨2, _⟩ => (k₀, i)

/-- The candidate vector `scalarBundle12_vec (j₀, k₀)` in `V_right`: sum of right-block basis tensors
indexed by `scalarBundle12_gR j₀ k₀ i` for `i ∈ Fin a`. -/
private noncomputable def scalarBundle12_vec (a b c : ℕ) (jk : Fin b × Fin c) :
    PiTensorProduct K (fun i : Sc (scalarBundle12_σ1 : Split (Fin 3)) => (MMObj K a b c).V i.val) :=
  ∑ i : Fin a, scalarBundle12_bR a b c (scalarBundle12_gR a b c jk.1 jk.2 i)

/-- A concrete element of `Sc scalarBundle12_σ1` with value `0`. -/
private noncomputable def scalarBundle12_sZeroC : Sc (scalarBundle12_σ1 : Split (Fin 3)) :=
  ⟨(0 : Fin 3), by
    show (0 : Fin 3) ∈ (scalarBundle12_σ1 : Split (Fin 3)).Sᶜ
    rw [Finset.mem_compl]
    intro h
    have : (0 : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) := h
    have h10 : (0 : Fin 3) = 1 := Finset.mem_singleton.mp this
    exact absurd h10 (by decide)⟩

/-- A concrete element of `Sc scalarBundle12_σ1` with value `2`. -/
private noncomputable def scalarBundle12_sTwoC : Sc (scalarBundle12_σ1 : Split (Fin 3)) :=
  ⟨(2 : Fin 3), by
    show (2 : Fin 3) ∈ (scalarBundle12_σ1 : Split (Fin 3)).Sᶜ
    rw [Finset.mem_compl]
    intro h
    have : (2 : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) := h
    have h12 : (2 : Fin 3) = 1 := Finset.mem_singleton.mp this
    exact absurd h12 (by decide)⟩

private lemma scalarBundle12_sZeroC_val : (scalarBundle12_sZeroC : Sc (scalarBundle12_σ1 : Split (Fin 3))).val = (0 : Fin 3) := rfl
private lemma scalarBundle12_sTwoC_val : (scalarBundle12_sTwoC : Sc (scalarBundle12_σ1 : Split (Fin 3))).val = (2 : Fin 3) := rfl

/-- `scalarBundle12_gR j₀ k₀ i` evaluated at `scalarBundle12_sZeroC` (mode-0 slot) gives `(i, j₀)`. -/
private lemma scalarBundle12_gR_at_sZeroC (a b c : ℕ) (j₀ : Fin b) (k₀ : Fin c) (i : Fin a) :
    (scalarBundle12_gR a b c j₀ k₀ i scalarBundle12_sZeroC : scalarBundle12_MMIdx a b c (scalarBundle12_sZeroC : Sc (scalarBundle12_σ1 : Split (Fin 3))).val) = (i, j₀) := by
  unfold scalarBundle12_gR
  rfl

/-- `scalarBundle12_gR j₀ k₀ i` evaluated at `scalarBundle12_sTwoC` (mode-2 slot) gives `(k₀, i)`. -/
private lemma scalarBundle12_gR_at_sTwoC (a b c : ℕ) (j₀ : Fin b) (k₀ : Fin c) (i : Fin a) :
    (scalarBundle12_gR a b c j₀ k₀ i scalarBundle12_sTwoC : scalarBundle12_MMIdx a b c (scalarBundle12_sTwoC : Sc (scalarBundle12_σ1 : Split (Fin 3))).val) = (k₀, i) := by
  unfold scalarBundle12_gR
  rfl

/-- The combined index `(jk, i) ↦ scalarBundle12_gR jk.1 jk.2 i` is injective. -/
private lemma scalarBundle12_gR_injective (a b c : ℕ) :
    Function.Injective (fun (p : (Fin b × Fin c) × Fin a) =>
      scalarBundle12_gR a b c p.1.1 p.1.2 p.2) := by
  rintro ⟨⟨j₀, k₀⟩, i⟩ ⟨⟨j₀', k₀'⟩, i'⟩ h
  simp only at h
  -- evaluate at scalarBundle12_sZeroC to get (i, j₀) = (i', j₀')
  have h1 : scalarBundle12_gR a b c j₀ k₀ i scalarBundle12_sZeroC = scalarBundle12_gR a b c j₀' k₀' i' scalarBundle12_sZeroC := by
    rw [h]
  rw [scalarBundle12_gR_at_sZeroC, scalarBundle12_gR_at_sZeroC] at h1
  -- evaluate at scalarBundle12_sTwoC to get (k₀, i) = (k₀', i')
  have h2 : scalarBundle12_gR a b c j₀ k₀ i scalarBundle12_sTwoC = scalarBundle12_gR a b c j₀' k₀' i' scalarBundle12_sTwoC := by
    rw [h]
  rw [scalarBundle12_gR_at_sTwoC, scalarBundle12_gR_at_sTwoC] at h2
  obtain ⟨hi, hj⟩ := Prod.mk.inj h1
  obtain ⟨hk, _⟩ := Prod.mk.inj h2
  simp [hi, hj, hk]

/-- For different `jk ≠ jk'`, the images `{scalarBundle12_gR jk.1 jk.2 i | i}` and
`{scalarBundle12_gR jk'.1 jk'.2 i | i}` are disjoint. -/
private lemma scalarBundle12_gR_disjoint (a b c : ℕ) {jk jk' : Fin b × Fin c} (hne : jk ≠ jk')
    (i i' : Fin a) :
    scalarBundle12_gR a b c jk.1 jk.2 i ≠ scalarBundle12_gR a b c jk'.1 jk'.2 i' := by
  intro h
  apply hne
  -- evaluate at scalarBundle12_sZeroC for j-component
  have h1 : scalarBundle12_gR a b c jk.1 jk.2 i scalarBundle12_sZeroC = scalarBundle12_gR a b c jk'.1 jk'.2 i' scalarBundle12_sZeroC := by rw [h]
  rw [scalarBundle12_gR_at_sZeroC, scalarBundle12_gR_at_sZeroC] at h1
  obtain ⟨_, hj⟩ := Prod.mk.inj h1
  -- evaluate at scalarBundle12_sTwoC for k-component
  have h2 : scalarBundle12_gR a b c jk.1 jk.2 i scalarBundle12_sTwoC = scalarBundle12_gR a b c jk'.1 jk'.2 i' scalarBundle12_sTwoC := by rw [h]
  rw [scalarBundle12_gR_at_sTwoC, scalarBundle12_gR_at_sTwoC] at h2
  obtain ⟨hk, _⟩ := Prod.mk.inj h2
  exact Prod.ext hj hk

/-- **Linear independence of `scalarBundle12_vec`.** Uses dual functionals:
the basis coord `scalarBundle12_bR.coord (scalarBundle12_gR jk.1 jk.2 ⟨0, ha⟩)` evaluates to 1 on `scalarBundle12_vec jk` and to 0
on `scalarBundle12_vec jk'` for `jk ≠ jk'`. -/
private lemma scalarBundle12_vec_linearIndependent (a b c : ℕ) (ha : 1 ≤ a) :
    LinearIndependent K (scalarBundle12_vec (K := K) a b c) := by
  -- the dual functional family
  let φ : Fin b × Fin c → Dual K
      (PiTensorProduct K (fun i : Sc (scalarBundle12_σ1 : Split (Fin 3)) =>
        (MMObj K a b c).V i.val)) :=
    fun jk => (scalarBundle12_bR a b c).coord (scalarBundle12_gR a b c jk.1 jk.2 ⟨0, ha⟩)
  refine LinearIndependent.of_pairwise_dual_eq_zero_one (v := scalarBundle12_vec a b c) (f := φ) ?_ ?_
  · intro jk jk' hne
    show φ jk (scalarBundle12_vec a b c jk') = 0
    unfold scalarBundle12_vec
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [Basis.coord_apply, Basis.repr_self_apply]
    rw [if_neg]
    intro h
    exact scalarBundle12_gR_disjoint a b c (Ne.symm hne) i ⟨0, ha⟩ h
  · intro jk
    show φ jk (scalarBundle12_vec a b c jk) = 1
    unfold scalarBundle12_vec
    rw [map_sum]
    rw [Finset.sum_eq_single (⟨0, ha⟩ : Fin a)]
    · rw [Basis.coord_apply, Basis.repr_self_apply, if_pos rfl]
    · intro i _ hi
      rw [Basis.coord_apply, Basis.repr_self_apply, if_neg]
      intro h
      have hinj := scalarBundle12_gR_injective a b c
      have : ((jk, i) : (Fin b × Fin c) × Fin a) = ((jk, ⟨0, ha⟩) : (Fin b × Fin c) × Fin a) := by
        apply hinj
        exact h
      have := (Prod.mk.inj this).2
      exact hi this
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Step 2: Each `scalarBundle12_vec jk` is in the range of the flattening map. -/

/-- The dual functional that "picks out coordinate `jk`" via the singleton
identification of the left block. Concretely: pull back the evaluation-at-`jk`
functional on `Fin b × Fin c → K` through `subsingletonEquiv scalarBundle12_sOneL`. -/
private noncomputable def scalarBundle12_dualL (a b c : ℕ) (jk : Fin b × Fin c) :
    Dual K (PiTensorProduct K (fun i : (scalarBundle12_σ1 : Split (Fin 3)).S =>
      (MMObj K a b c).V i.val)) :=
  (LinearMap.proj jk : (Fin b × Fin c → K) →ₗ[K] K).comp
    ((PiTensorProduct.subsingletonEquiv scalarBundle12_sOneL).toLinearMap :
      PiTensorProduct K (fun i : (scalarBundle12_σ1 : Split (Fin 3)).S =>
        (MMObj K a b c).V i.val) →ₗ[K] (Fin b × Fin c → K))

/-- `scalarBundle12_dualL jk` applied to a pure tensor `tprod K v` evaluates `v scalarBundle12_sOneL` at `jk`. -/
private lemma scalarBundle12_dualL_tprod (a b c : ℕ) (jk : Fin b × Fin c)
    (v : ∀ s : (scalarBundle12_σ1 : Split (Fin 3)).S, (MMObj K a b c).V s.val) :
    scalarBundle12_dualL a b c jk (tprod K v) = (v scalarBundle12_sOneL : Fin b × Fin c → K) jk := by
  unfold scalarBundle12_dualL
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  have h : (PiTensorProduct.subsingletonEquiv scalarBundle12_sOneL : PiTensorProduct K
      (fun i : (scalarBundle12_σ1 : Split (Fin 3)).S => (MMObj K a b c).V i.val) ≃ₗ[K]
      (MMObj K a b c).V (scalarBundle12_sOneL : (scalarBundle12_σ1 : Split (Fin 3)).S).val) (tprod K v) =
      v scalarBundle12_sOneL :=
    PiTensorProduct.subsingletonEquiv_apply_tprod _ _
  show (PiTensorProduct.subsingletonEquiv scalarBundle12_sOneL) (tprod K v) jk = v scalarBundle12_sOneL jk
  rw [h]

/-- The mode-wise data function for the (i, j, k) term of `MMTensor K a b c`. -/
private noncomputable def scalarBundle12_modeData (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    ∀ s : Fin 3, MMSpace K a b c s := fun s =>
  match s with
  | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin a × Fin b → K)
  | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin b × Fin c → K)
  | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin c × Fin a → K)

/-- `MMTensor K a b c` written as a triple sum using `scalarBundle12_modeData`. -/
private lemma scalarBundle12_MMTensor_eq_sum (a b c : ℕ) :
    MMTensor K a b c = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
      tprod K (scalarBundle12_modeData (K := K) a b c i j k) := by
  rfl

/-- The "left" tensor of the (i, j, k) term after `splitTensorEquiv scalarBundle12_σ1`. -/
private noncomputable def scalarBundle12_Lterm (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct K (fun s : (scalarBundle12_σ1 : Split (Fin 3)).S => (MMObj K a b c).V s.val) :=
  tprod K (fun s : (scalarBundle12_σ1 : Split (Fin 3)).S => scalarBundle12_modeData a b c i j k s.val)

/-- The "right" tensor of the (i, j, k) term after `splitTensorEquiv scalarBundle12_σ1`. -/
private noncomputable def scalarBundle12_Rterm (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct K (fun s : Sc (scalarBundle12_σ1 : Split (Fin 3)) => (MMObj K a b c).V s.val) :=
  tprod K (fun s : Sc (scalarBundle12_σ1 : Split (Fin 3)) => scalarBundle12_modeData a b c i j k s.val)

/-- `splitTensorEquiv` of one pure term decomposes into `scalarBundle12_Lterm ⊗ₜ scalarBundle12_Rterm`. -/
private lemma scalarBundle12_splitTensorEquiv_term (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    splitTensorEquiv scalarBundle12_σ1 (tprod K (scalarBundle12_modeData (K := K) a b c i j k))
      = scalarBundle12_Lterm a b c i j k ⊗ₜ[K] scalarBundle12_Rterm a b c i j k :=
  splitTensorEquiv_tprod _ _

/-- The `scalarBundle12_dualL jk` value on `scalarBundle12_Lterm i j k` is `δ_{(j,k) = jk}`. -/
private lemma scalarBundle12_dualL_Lterm (a b c : ℕ) (jk : Fin b × Fin c)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    scalarBundle12_dualL a b c jk (scalarBundle12_Lterm a b c i j k) = if (j, k) = jk then (1 : K) else 0 := by
  unfold scalarBundle12_Lterm
  rw [scalarBundle12_dualL_tprod]
  show (scalarBundle12_modeData (K := K) a b c i j k (scalarBundle12_sOneL : (scalarBundle12_σ1 : Split (Fin 3)).S).val :
    Fin b × Fin c → K) jk = if (j, k) = jk then (1 : K) else 0
  rw [show scalarBundle12_modeData (K := K) a b c i j k (scalarBundle12_sOneL : (scalarBundle12_σ1 : Split (Fin 3)).S).val =
      (Pi.single (j, k) 1 : Fin b × Fin c → K) from rfl]
  rw [Pi.single_apply]
  by_cases h : jk = (j, k)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- `scalarBundle12_Rterm i j k = scalarBundle12_bR (scalarBundle12_gR j k i)`. -/
private lemma scalarBundle12_Rterm_eq_bR (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    (scalarBundle12_Rterm (K := K) a b c i j k) = scalarBundle12_bR (K := K) a b c (scalarBundle12_gR a b c j k i) := by
  unfold scalarBundle12_Rterm scalarBundle12_bR
  rw [Basis.piTensorProduct_apply]
  congr 1
  funext s
  show scalarBundle12_modeData (K := K) a b c i j k s.val = scalarBundle12_MMBasis K a b c s.val (scalarBundle12_gR a b c j k i s)
  rcases s with ⟨sv, hsv⟩
  have hne : sv ≠ 1 := scalarBundle12_sc_ne_one ⟨sv, hsv⟩
  match sv, hne with
  | ⟨0, hsv0⟩, _ =>
    show (Pi.single (i, j) 1 : Fin a × Fin b → K) =
      scalarBundle12_MMBasis K a b c (⟨0, hsv0⟩ : Fin 3) (scalarBundle12_gR a b c j k i ⟨⟨0, hsv0⟩, hsv⟩)
    show (Pi.single (i, j) 1 : Fin a × Fin b → K) =
      Pi.basisFun K (Fin a × Fin b) (scalarBundle12_gR a b c j k i ⟨⟨0, hsv0⟩, hsv⟩)
    rw [Pi.basisFun_apply]
    rfl
  | ⟨2, hsv2⟩, _ =>
    show (Pi.single (k, i) 1 : Fin c × Fin a → K) =
      scalarBundle12_MMBasis K a b c (⟨2, hsv2⟩ : Fin 3) (scalarBundle12_gR a b c j k i ⟨⟨2, hsv2⟩, hsv⟩)
    show (Pi.single (k, i) 1 : Fin c × Fin a → K) =
      Pi.basisFun K (Fin c × Fin a) (scalarBundle12_gR a b c j k i ⟨⟨2, hsv2⟩, hsv⟩)
    rw [Pi.basisFun_apply]
    rfl
  | ⟨1, _⟩, h => exact absurd rfl h

/-- The key formula expressing `flatteningMap scalarBundle12_σ1 (MMObj K a b c) (scalarBundle12_dualL jk)` as
`∑_{i,j,k} δ_{(j,k)=jk} • scalarBundle12_bR (scalarBundle12_gR j k i) = scalarBundle12_vec jk`. -/
private lemma scalarBundle12_flatteningMap_MMObj_dualL_eq_vec (a b c : ℕ) (jk : Fin b × Fin c) :
    flatteningMap scalarBundle12_σ1 (MMObj K a b c) (scalarBundle12_dualL a b c jk) = scalarBundle12_vec a b c jk := by
  unfold flatteningMap
  show tensorToDualHom K _ _ (splitTensorEquiv scalarBundle12_σ1 (MMTensor K a b c)) (scalarBundle12_dualL a b c jk) =
    scalarBundle12_vec a b c jk
  rw [scalarBundle12_MMTensor_eq_sum]
  rw [show splitTensorEquiv scalarBundle12_σ1 (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        tprod K (scalarBundle12_modeData (K := K) a b c i j k))
      = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        scalarBundle12_Lterm a b c i j k ⊗ₜ[K] scalarBundle12_Rterm a b c i j k from ?_]
  swap
  · simp only [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact scalarBundle12_splitTensorEquiv_term a b c i j k
  have hreduce : ((tensorToDualHom K
      (PiTensorProduct K (fun s : (scalarBundle12_σ1 : Split (Fin 3)).S => (MMObj K a b c).V s.val))
      (PiTensorProduct K (fun s : Sc (scalarBundle12_σ1 : Split (Fin 3)) => (MMObj K a b c).V s.val)))
      (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        scalarBundle12_Lterm a b c i j k ⊗ₜ[K] scalarBundle12_Rterm a b c i j k)) (scalarBundle12_dualL a b c jk) =
      ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        scalarBundle12_dualL (K := K) a b c jk (scalarBundle12_Lterm a b c i j k) • scalarBundle12_Rterm (K := K) a b c i j k := by
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [tensorToDualHom_tmul]
  change ((tensorToDualHom K
      (PiTensorProduct K (fun s : (scalarBundle12_σ1 : Split (Fin 3)).S => (MMObj K a b c).V s.val))
      (PiTensorProduct K (fun s : Sc (scalarBundle12_σ1 : Split (Fin 3)) => (MMObj K a b c).V s.val)))
      (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        scalarBundle12_Lterm a b c i j k ⊗ₜ[K] scalarBundle12_Rterm a b c i j k)) (scalarBundle12_dualL a b c jk) = _
  rw [hreduce]
  simp_rw [scalarBundle12_dualL_Lterm]
  simp_rw [scalarBundle12_Rterm_eq_bR]
  -- Goal:
  -- ∑ i, ∑ j, ∑ k, (if (j,k) = jk then 1 else 0) • scalarBundle12_bR (scalarBundle12_gR j k i) = scalarBundle12_vec jk
  -- scalarBundle12_vec jk = ∑_i scalarBundle12_bR (scalarBundle12_gR jk.1 jk.2 i).
  -- For fixed i, the inner ∑_{j,k} selects (j,k) = jk.
  -- Strategy: collapse j, k for each i.
  unfold scalarBundle12_vec
  -- Goal: ∑ i, ∑ j, ∑ k, (if (j,k) = jk then 1 else 0) • scalarBundle12_bR (scalarBundle12_gR j k i) =
  --       ∑ i, scalarBundle12_bR (scalarBundle12_gR jk.1 jk.2 i)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- For each i, collapse the (j, k) double sum.
  rw [Finset.sum_eq_single jk.1]
  · rw [Finset.sum_eq_single jk.2]
    · rw [if_pos rfl, one_smul]
    · intro k _ hk
      rw [if_neg, zero_smul]
      intro h
      apply hk
      exact (Prod.mk.inj h).2
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j _ hj
    rw [Finset.sum_eq_zero]
    intro k _
    rw [if_neg, zero_smul]
    intro h
    apply hj
    exact (Prod.mk.inj h).1
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`scalarBundle12_vec jk ∈ range (flatteningMap scalarBundle12_σ1 (MMObj K a b c))`.** -/
private lemma scalarBundle12_vec_mem_range (a b c : ℕ) (jk : Fin b × Fin c) :
    scalarBundle12_vec a b c jk ∈ LinearMap.range (flatteningMap scalarBundle12_σ1 (MMObj K a b c)) := by
  exact ⟨scalarBundle12_dualL a b c jk, scalarBundle12_flatteningMap_MMObj_dualL_eq_vec a b c jk⟩

end MMObj_bc

end MMEFlatteningRankMMObjBcSol

/-! ### Main result (top-level for platform upload) -/

open MMEFlatteningRankMMObjBcSol MME

/-- The mode-1 flattening rank of `MMObj K a b c` is at least `b * c` when `a ≥ 1`.

Proof: we construct `b * c` linearly independent vectors `scalarBundle12_vec jk` for `jk ∈ Fin b × Fin c`
in the range of the flattening map. Each `scalarBundle12_vec jk = ∑_i scalarBundle12_bR (scalarBundle12_gR jk.1 jk.2 i)` is a sum of
right-block basis tensors, and the index map `(jk, i) ↦ scalarBundle12_gR jk.1 jk.2 i` is injective;
combined with `a ≥ 1`, this yields linear independence. -/
theorem mme_flatteningRank_MMObj_bc {K : Type u} [Field K] (a b c : ℕ) (ha : 1 ≤ a) :
    b * c ≤ MME.flatteningRank MME.split1 (MME.MMObj K a b c) := by
  unfold flatteningRank
  set V_right := PiTensorProduct K (fun i : Sc (scalarBundle12_σ1 : Split (Fin 3)) =>
    (MMObj K a b c).V i.val) with hVright
  haveI : FiniteDimensional K V_right :=
    Module.Finite.of_basis (scalarBundle12_bR a b c)
  set rangeFM := LinearMap.range (flatteningMap scalarBundle12_σ1 (MMObj K a b c)) with hrangeFM
  let vecInRange : Fin b × Fin c → rangeFM := fun jk =>
    ⟨scalarBundle12_vec a b c jk, scalarBundle12_vec_mem_range a b c jk⟩
  have hLI : LinearIndependent K vecInRange := by
    have hLI₀ : LinearIndependent K (scalarBundle12_vec (K := K) a b c) :=
      scalarBundle12_vec_linearIndependent a b c ha
    exact hLI₀.of_comp rangeFM.subtype
  have hcard : Fintype.card (Fin b × Fin c) = b * c := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have := hLI.fintype_card_le_finrank (R := K) (M := rangeFM)
  rw [hcard] at this
  exact this

end

section
-- ScalarRegionalStep

open BigOperators MME MME.ProfiledCW MME.RegionRealization MME.RecursiveYZ
open MME.CompleteSplit MME.RecursiveThinSplit

namespace ScalarRegionalStep

def parent : Fin 1 → Fin 3 → ℕ := fun _ ↦ ![4, 0, 0]
abbrev counts : Fin 1 → ℕ := fun _ ↦ 1

def left : Split 2 (parent 0) := ⟨![2, 0, 0], by decide⟩

lemma split_eq (r : Fin 1) (a : Split 2 (parent r)) : a = left := by
  have hr : r = 0 := Subsingleton.elim _ _
  subst r
  apply Subtype.ext
  funext i
  have h1 := a.property.2 1
  have h2 := a.property.2 2
  have hs := a.property.1
  simp [parent] at h1 h2
  fin_cases i <;> apply Fin.ext <;> simp [left] <;> omega

def positions : Fin 2 ≃ Position counts where
  toFun p := ⟨0, 0, p⟩
  invFun p := p.2.2
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨r, t, h⟩
    have hr : r = 0 := Subsingleton.elim _ _
    have ht : t = 0 := Subsingleton.elim _ _
    subst r
    subst t
    rfl

def hashPositions : Fin 1 ≃ (r : Fin 1) × Fin (counts r) where
  toFun _ := ⟨0, 0⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv p := by
    rcases p with ⟨r, t⟩
    fin_cases r
    fin_cases t
    rfl

def mu (i : Fin 3) (_ : Cell 2 1 parent) (w : CompleteWord 1) : ℕ :=
  if w 0 = left.val i then 2 else 0

lemma word_eq (w : CompleteWord 1) : w = fun _ ↦ w 0 := by
  funext r
  fin_cases r
  rfl

/-- A valid two-position regional step supported on the scalar split `(2,0,0)`. -/
noncomputable def step : IntegerStep 1 2 (fun _ _ ↦ True) where
  half := 2
  R := 1
  parent := parent
  n := counts
  total := by intro r; rfl
  half_eq := by norm_num
  m := fun _ _ ↦ 1
  N := 0
  hashPositions := hashPositions
  L := 2
  positions := positions
  length := by norm_num
  mu := mu
  mass := by
    intro i c
    classical
    change (∑ w : CompleteWord 1, mu i c w) = 2
    rw [Finset.sum_eq_single (fun _ ↦ left.val i)]
    · simp [mu]
    · intro w _ hw
      have hn : w 0 ≠ left.val i := by
        intro h
        apply hw
        rw [word_eq w, h]
      simp [mu, hn]
    · simp
  support := by
    intro i c w hw
    have hc := split_eq c.1 c.2
    have h : w 0 = left.val i := by
      by_contra h
      simp [mu, h] at hw
    simp [h, hc]
  boundary := by
    constructor
    · intro c hc w
      rw [split_eq c.1 c.2] at hc
      have hh : Fin.rev (w 0) = (2 : Fin 3) ↔ w 0 = 0 := by
        constructor <;> intro h <;> apply Fin.ext <;>
          have := congrArg Fin.val h <;> simp [Fin.rev] at * <;> omega
      simp [mu, left, hh]
    constructor
    · intro c hc
      rw [split_eq c.1 c.2] at hc
      norm_num [left] at hc
    · intro c hc w
      have hh : Fin.rev (w 0) = (2 : Fin 3) ↔ w 0 = 0 := by
        constructor <;> intro h <;> apply Fin.ext <;>
          have := congrArg Fin.val h <;> simp [Fin.rev] at * <;> omega
      simp [mu, left, hh]
  reference := fun _ _ ↦ left
  reference_target := by
    classical
    simp only [RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ, true_and]
    intro r a
    rw [split_eq r a]
    simp [RecursiveThinSplit.count]
  minimum := 1
  repairScale := 2
  minimum_pos := by decide
  repairScale_gt_one := by decide
  parent_size := by intro r; rfl
  split_divisible := by simp
  epsilon := 100
  epsilon_pos := by norm_num
  size_test := by norm_num [CompleteWord, Fintype.card_fun]
  source_inside := by intros; trivial

theorem output_scalar (i : Fin 3) (x : FineWord 2)
    (h : step.output i x) : x = fun _ ↦ left.val i := by
  funext r
  apply Fin.ext
  have hg := h.1 (positions r)
  fin_cases i <;> fin_cases r <;>
    simpa [step, positions, split, fullCell, complement, left, parent,
      Fin.sum_univ_succ] using hg

theorem scalar_output (i : Fin 3) : step.output i (fun _ ↦ left.val i) := by
  classical
  constructor
  · intro p
    rcases p with ⟨r, t, h⟩
    fin_cases r
    fin_cases t
    fin_cases h <;> fin_cases i <;>
      simp [step, positions, split, fullCell, complement, left, parent]
  · intro c w
    rcases c with ⟨r, a⟩
    have ha := split_eq r a
    fin_cases r
    subst a
    have hc (p : Position counts) :
        fullCell step.total step.reference p = ⟨(0 : Fin 1), left⟩ := by
      rcases p with ⟨r, t, h⟩
      fin_cases r
      dsimp only [fullCell, step]
      apply Sigma.ext (by rfl)
      apply heq_of_eq
      exact split_eq _ _
    change RecursiveYZ.count (fullCell step.total step.reference)
      (ProfiledCW.split step.positions step.length (fun _ ↦ left.val i))
      ⟨(0 : Fin 1), left⟩ w = mu i ⟨(0 : Fin 1), left⟩ w
    simp only [RecursiveYZ.count, hc, true_and]
    change (Finset.univ.filter (fun _ : Position counts ↦
      (fun _ : Fin (2 ^ (1 - 1)) ↦ left.val i) = w)).card = mu i ⟨0, left⟩ w
    have he : (fun _ : Fin (2 ^ (1 - 1)) ↦ left.val i) = w ↔
        w 0 = left.val i := by
      constructor
      · intro h
        exact (congrFun h 0).symm
      · intro h
        rw [word_eq w, h]
    by_cases h : w 0 = left.val i
    · have hf := he.mpr h
      rw [Finset.filter_eq_self.mpr (fun _ _ ↦ hf)]
      simp [h, mu, Position, Fintype.card_sigma]
    · have hf : (fun _ : Fin (2 ^ (1 - 1)) ↦ left.val i) ≠ w :=
        fun hh ↦ h (he.mp hh)
      rw [Finset.filter_eq_empty_iff.mpr (fun _ _ ↦ hf)]
      simp [h, mu]

/-- Each mode admits exactly its constant scalar word. -/
theorem output_iff (i : Fin 3) (x : FineWord 2) :
    step.output i x ↔ x = fun _ ↦ left.val i := by
  constructor
  · exact output_scalar i x
  · rintro rfl
    exact scalar_output i

end ScalarRegionalStep


end

section
-- ScalarRegionalBoundary

open MME MME.ProfiledCW MME.TensorObj MME.RegionRealization Module
set_option autoImplicit false

namespace ScalarRegionalStep

def coordinate (i : Fin 3) : Coordinate 2 := fun _ ↦
  ULift.up (if i = 0 then 6 else 0)

lemma coordinate_unique (i : Fin 3) (x : Coordinate 2)
    (hx : step.output i (fine x)) : x = coordinate i := by
  have h := output_scalar i (fine x) hx
  funext r
  apply ULift.ext
  apply Fin.ext
  have hr := congrFun h r
  fin_cases i <;>
    simp [fine, left, cwSquareCoordGrade, coordinate] at * <;>
    split_ifs at hr <;> simp_all

/-- The scalar regional output spans at most one coordinate in each mode. -/
theorem mode_finrank_le_one (K : Type) [Field K] (i : Fin 3) :
    finrank K ((tensor K step.output).V i) ≤ 1 := by
  classical
  let b := canonical K 2 i
  let S : Submodule K ((raw K 2).V i) :=
    Submodule.span K (b '' {x | (if step.output i (fine x) then (0 : Fin 2) else 1) = 0})
  change finrank K S ≤ 1
  have hs : S ≤ Submodule.span K {b (coordinate i)} := by
    apply Submodule.span_mono
    rintro _ ⟨x, hx, rfl⟩
    have hx' : step.output i (fine x) := by
      by_contra hn
      simp [hn] at hx
    rw [coordinate_unique i x hx']
    exact Set.mem_singleton _
  apply (Submodule.finrank_mono hs).trans
  simpa using finrank_span_le_card (R := K) {b (coordinate i)}

/-- Flattening ranks cannot exceed one when all mode spaces have dimension at most one. -/
theorem flattening_rank_le_one (K : Type) [Field K] (σ : MME.Split (Fin 3)) :
    flatteningRank σ (tensor K step.output) ≤ 1 := by
  classical
  let X := tensor K step.output
  let b := Basis.piTensorProduct (fun i : Sc σ ↦ Free.chooseBasis K (X.V i))
  haveI := Module.Finite.of_basis b
  have hd : finrank K (PiTensorProduct K (fun i : Sc σ ↦ X.V i)) ≤ 1 := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_pi]
    apply Finset.prod_le_one (fun _ _ ↦ Nat.zero_le _)
    intro i _
    rw [← Module.finrank_eq_card_basis (Free.chooseBasis K (X.V i))]
    exact mode_finrank_le_one K i
  exact (Submodule.finrank_le _).trans hd

/-- No matrix block of volume greater than one can be extracted from this output. -/
theorem matrix_volume_le_one (a b c : ℕ)
    (h : Restrict (MMObj ℚ a b c) (tensor ℚ step.output)) : a * b * c ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  by_cases hc : c = 0
  · simp [hc]
  have ha' : 1 ≤ a := by omega
  have hb' : 1 ≤ b := by omega
  have hc' : 1 ≤ c := by omega
  have hab := (mme_flatteningRank_MMObj_ab (K := ℚ) a b c hc').trans
    ((flatteningRank_mono _ h).trans (flattening_rank_le_one ℚ _))
  have hbc := (mme_flatteningRank_MMObj_bc (K := ℚ) a b c ha').trans
    ((flatteningRank_mono _ h).trans (flattening_rank_le_one ℚ _))
  have ha1 : a = 1 := by nlinarith
  have hb1 : b = 1 := by nlinarith
  have hc1 : c = 1 := by nlinarith
  simp [ha1, hb1, hc1]

theorem boundary_volume_le_one (B : BoundaryEnd 1 2 step.output) :
    B.a * B.b * B.c ≤ 1 :=
  matrix_volume_le_one B.a B.b B.c (mme_recursive_profiled_CW_boundary_end B)

theorem boundary_match_false : ¬ (∀ (lower : ℕ)
    (S : IntegerStep lower 2 (fun _ _ ↦ True)),
    ∃ B : BoundaryEnd lower 2 S.output,
      B.a * B.b * B.c = 25 ∧ 1 ≤ B.a * B.b * B.c) := by
  intro h
  obtain ⟨B, hB, _⟩ := h 1 step
  have := boundary_volume_le_one B
  omega

end ScalarRegionalStep




end

open MME.ProfiledCW MME.RegionRealization

theorem solution : ¬ (∀ (lower : ℕ)
    (S : IntegerStep lower 2 (fun _ _ ↦ True)),
    ∃ B : BoundaryEnd lower 2 S.output,
      B.a * B.b * B.c = 25 ∧ 1 ≤ B.a * B.b * B.c) :=
  ScalarRegionalStep.boundary_match_false

#print axioms solution
