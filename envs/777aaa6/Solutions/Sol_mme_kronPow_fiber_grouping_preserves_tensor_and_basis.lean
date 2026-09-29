-- Prove2me | solution 1 for mme_kronPow_fiber_grouping_preserves_tensor_and_basis
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T11:59:39.304132+00:00
-- url     : https://prove2.me/submissions/cdd65aa8-83bf-4484-936a-44d025aa2afe

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_mme_kronFin_mode_pi_basis

open MME MME.TensorObj PiTensorProduct TensorProduct BigOperators Module

universe u

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

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
  simp [Basis.piTensorProduct_apply,
    Module.Basis.reindex_apply]

private theorem basis_repr_equiv_explicit
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
private theorem kronPowModeWordBasis_succ_apply_explicit
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

private noncomputable def kronPowTensorWordBasisExplicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i)) (n : ℕ) :
    Basis (∀ i, Fin n → ι i) K
      (PiTensorProduct K (fun i ↦ (T.kronPow n).V i)) :=
  Basis.piTensorProduct
    (fun i ↦ kronPowModeWordBasis T i (b i) n)

private theorem kronPowTensorWordBasis_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i))
    (n : ℕ) (w : ∀ i, Fin n → ι i) :
    (kronPowTensorWordBasisExplicit T b n).repr (T.kronPow n).t w =
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
          (kronPowTensorWordBasisExplicit T b n).repr (T.kronPow n).t
            (fun i r ↦ w i r.succ) = _
      rw [ih]
      rw [Fin.prod_univ_succ]

private theorem finite_product_coeff
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
      rw [piTensorProduct_basis_reindex_explicit, Module.Basis.repr_reindex_apply,
        interchange_basis_repr_explicit]
      simp only [Equiv.piCongrRight_symm_apply, Pi.map_apply, Fin.consEquiv_symm_apply]
      rw [ih, Fin.prod_univ_succ]
      rfl

private theorem map_basis_equiv_coeff
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
      exact basis_repr_equiv_explicit (b i) (c i) (e i) (v i) (w i)
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem solution {K : Type u} [Field K] {d N k : ℕ}
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
    rw [map_basis_equiv_coeff (T.kronPow N) S B C e]
    change (kronPowTensorWordBasisExplicit T b N).repr (T.kronPow N).t
      (fun i r ↦ w i (positions r).1 (positions r).2) = _
    rw [kronPowTensorWordBasis_repr_explicit, finite_product_coeff]
    change _ = ∏ j, (kronPowTensorWordBasisExplicit T b (count j)).repr
      (T.kronPow (count j)).t (fun i ↦ w i j)
    simp_rw [kronPowTensorWordBasis_repr_explicit]
    calc
      _ = ∏ p : Σ j, Fin (count j),
          (Basis.piTensorProduct b).repr T.t (fun i ↦ w i p.1 p.2) :=
        Equiv.prod_comp positions _
      _ = _ := Fintype.prod_sigma _
  · intro i w
    exact Basis.equiv_apply _ _ _ _
