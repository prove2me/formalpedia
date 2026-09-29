-- Prove2me | solution 1 for mme_profiled_CW_mode_permutation_iso
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T15:16:54.444172+00:00
-- url     : https://prove2.me/submissions/b418f8e0-5905-4056-aa92-846227b0b9b1

import Theorems.Thm_mme_basis_projected_mode_permutation_iso
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_CW_three_canonical_support
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Algebra.BigOperators.Fin

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

private noncomputable def bbase (K : Type u) [Field K] :
    ∀ i : Fin 3, Basis (ULift.{u} (Fin 7)) K ((CWObj K 5).V i) :=
  fun i ↦ (cwThreeCanonicalBasis K 5 i).reindex Equiv.ulift.symm

private theorem monom_basis {K : Type u} [Field K] (a b c : Fin 7) :
    CWMonom K 5 a b c = (Basis.piTensorProduct (bbase K)) ![ULift.up a,ULift.up b,ULift.up c] := by
  rw [Basis.piTensorProduct_apply]
  unfold CWMonom
  congr 1
  funext i
  fin_cases i <;> dsimp only [bbase, cwThreeCanonicalBasis] <;>
    rw [Basis.reindex_apply]
  · exact (Pi.basisFun_apply K (Fin 7) a).symm
  · exact (Pi.basisFun_apply K (Fin 7) b).symm
  · exact (Pi.basisFun_apply K (Fin 7) c).symm

private theorem base_expansion {K : Type u} [Field K] :
    (CWObj K 5).t =
      (∑ k : Fin 5, (
        (Basis.piTensorProduct (bbase K)) ![ULift.up 0,ULift.up (⟨k.val+1,by omega⟩ : Fin 7),ULift.up ⟨k.val+1,by omega⟩] +
        (Basis.piTensorProduct (bbase K)) ![ULift.up ⟨k.val+1,by omega⟩,ULift.up 0,ULift.up ⟨k.val+1,by omega⟩] +
        (Basis.piTensorProduct (bbase K)) ![ULift.up ⟨k.val+1,by omega⟩,ULift.up ⟨k.val+1,by omega⟩,ULift.up 0])) +
      (Basis.piTensorProduct (bbase K)) ![ULift.up 0,ULift.up 0,ULift.up 6] +
      (Basis.piTensorProduct (bbase K)) ![ULift.up 0,ULift.up 6,ULift.up 0] +
      (Basis.piTensorProduct (bbase K)) ![ULift.up 6,ULift.up 0,ULift.up 0] := by
  simp only [← monom_basis]
  rfl


private theorem cycle_tuple {I : Type*} (a b c : I) (x : Fin 3 → I) :
    (![a,b,c] = fun i ↦ x (cyclicPerm i)) ↔ ![c,a,b] = x := by
  simp [funext_iff, Fin.forall_fin_succ, cyclicPerm, and_comm, and_left_comm, and_assoc]

private theorem swap_tuple {I : Type*} (a b c : I) (x : Fin 3 → I) :
    (![a,b,c] = fun i ↦ x (swapFirstTwoPerm i)) ↔ ![b,a,c] = x := by
  simp [funext_iff, Fin.forall_fin_succ, swapFirstTwoPerm, and_comm, and_left_comm, and_assoc]

private theorem base_cycle {K : Type u} [Field K] (x : Fin 3 → ULift.{u} (Fin 7)) :
    (Basis.piTensorProduct (bbase K)).repr (CWObj K 5).t (fun i ↦ x (cyclicPerm i)) =
      (Basis.piTensorProduct (bbase K)).repr (CWObj K 5).t x := by
  classical
  have h := base_expansion (K := K)
  generalize (Basis.piTensorProduct (bbase K)) = BB at h ⊢
  rw [h]
  simp only [map_add, map_sum, Finsupp.finset_sum_apply, Finsupp.add_apply,
    Basis.repr_self, Finsupp.single_apply]
  simp only [cycle_tuple]
  simp only [Finset.sum_add_distrib]
  ring

private theorem base_swap {K : Type u} [Field K] (x : Fin 3 → ULift.{u} (Fin 7)) :
    (Basis.piTensorProduct (bbase K)).repr (CWObj K 5).t (fun i ↦ x (swapFirstTwoPerm i)) =
      (Basis.piTensorProduct (bbase K)).repr (CWObj K 5).t x := by
  classical
  have h := base_expansion (K := K)
  generalize (Basis.piTensorProduct (bbase K)) = BB at h ⊢
  rw [h]
  simp only [map_add, map_sum, Finsupp.finset_sum_apply, Finsupp.add_apply,
    Basis.repr_self, Finsupp.single_apply]
  simp only [swap_tuple]
  simp only [Finset.sum_add_distrib]
  ring

private theorem power_symmetric {K : Type u} [Field K] (N : ℕ)
    (sigma : Equiv.Perm (Fin 3))
    (hbase : ∀ x : Fin 3 → ULift.{u} (Fin 7),
      (Basis.piTensorProduct (bbase K)).repr (CWObj K 5).t (fun i ↦ x (sigma i)) =
        (Basis.piTensorProduct (bbase K)).repr (CWObj K 5).t x)
    (x : Fin 3 → Coordinate.{u} N) :
    (Basis.piTensorProduct (canonical K N)).repr (raw K N).t (fun i ↦ x (sigma i)) =
      (Basis.piTensorProduct (canonical K N)).repr (raw K N).t x := by
  calc
    _ = ∏ r : Fin N, (Basis.piTensorProduct (bbase K)).repr (CWObj K 5).t
        (fun i ↦ x (sigma i) r) := power_coefficient_product (CWObj K 5) (bbase K) N _
    _ = ∏ r : Fin N, (Basis.piTensorProduct (bbase K)).repr (CWObj K 5).t
        (fun i ↦ x i r) := Finset.prod_congr rfl (fun r _ ↦ hbase (fun i ↦ x i r))
    _ = _ := (power_coefficient_product (CWObj K 5) (bbase K) N x).symm

theorem solution {K : Type u} [Field K] {N : ℕ} (P : Predicate N)
    (sigma : Equiv.Perm (Fin 3)) (h : sigma = cyclicPerm ∨ sigma = swapFirstTwoPerm) :
    Isomorphic (tensor K (fun i ↦ P (sigma.symm i))) (permObj sigma (tensor K P)) := by
  apply mme_basis_projected_mode_permutation_iso (raw K N) (canonical K N) sigma
    (fun i x ↦ P i (fine x))
  rcases h with rfl | rfl
  · exact power_symmetric N cyclicPerm base_cycle
  · exact power_symmetric N swapFirstTwoPerm base_swap
