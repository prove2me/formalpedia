-- Prove2me | solution 1 for mme_cwFourth_kronPow_word_basis_coefficients_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T10:25:12.570669+00:00
-- url     : https://prove2.me/submissions/318b4ecd-23f1-4114-afed-f928fef24410

import Theorems.Thm_mme_basis_projected_mode_permutation_iso
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_six_symmetrized_tau_value
import Mathlib.Algebra.BigOperators.Fin

open MME MME.TensorObj MME.StothersFourth MME.DWZStep1Support MME.CompleteSplit
open PiTensorProduct TensorProduct BigOperators Module

universe u

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace MME.DWZFourthSymmetry

theorem interchange_tprod_explicit
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

theorem interchange_basis_repr_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {ι κ : Fin d → Type*}
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

theorem piTensorProduct_basis_reindex_explicit
    {K : Type u} [Field K] {d : ℕ}
    {V : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    {ι κ : Fin d → Type*}
    (b : ∀ i, Basis (ι i) K (V i))
    (e : ∀ i, ι i ≃ κ i) :
    Basis.piTensorProduct (fun i ↦ (b i).reindex (e i)) =
      (Basis.piTensorProduct b).reindex (Equiv.piCongrRight e) := by
  ext w
  simp [Basis.piTensorProduct_apply, Module.Basis.reindex_apply]

noncomputable def powerBasis
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (T.V i)) (n : ℕ) :
    Basis (∀ i, Fin n → ι i) K
      (PiTensorProduct K (fun i ↦ (T.kronPow n).V i)) :=
  Basis.piTensorProduct (fun i ↦ kronPowModeWordBasis T i (b i) n)

theorem power_coefficient_product
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

/-! ## Symmetry of the CW coefficients -/

/-- Invariance of a coefficient function under precomposition with `σ`. -/
def SymUnder {I M : Type*} (f : (Fin 3 → I) → M) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ x : Fin 3 → I, f (fun i ↦ x (σ i)) = f x

theorem SymUnder.mul {I M : Type*} {f : (Fin 3 → I) → M} {σ τ : Equiv.Perm (Fin 3)}
    (hσ : SymUnder f σ) (hτ : SymUnder f τ) : SymUnder f (σ * τ) := by
  intro x
  exact (hτ (fun j ↦ x (σ j))).trans (hσ x)

theorem SymUnder.one {I M : Type*} (f : (Fin 3 → I) → M) : SymUnder f 1 := fun _ ↦ rfl

theorem perm_cases (σ : Equiv.Perm (Fin 3)) :
    σ = 1 ∨ σ = cyclicPerm ∨ σ = cyclicPerm * cyclicPerm ∨ σ = swapFirstTwoPerm ∨
      σ = swapFirstTwoPerm * cyclicPerm ∨ σ = swapFirstTwoPerm * (cyclicPerm * cyclicPerm) := by
  revert σ
  decide

theorem SymUnder.all {I M : Type*} {f : (Fin 3 → I) → M}
    (hc : SymUnder f cyclicPerm) (hs : SymUnder f swapFirstTwoPerm) (σ : Equiv.Perm (Fin 3)) :
    SymUnder f σ := by
  rcases perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SymUnder.one f
  · exact hc
  · exact hc.mul hc
  · exact hs
  · exact hs.mul hc
  · exact hs.mul (hc.mul hc)

/-- The canonical CW basis, unlifted. -/
noncomputable def cb (K : Type u) [Field K] : ∀ i : Fin 3, Basis (Fin 7) K ((CWObj K 5).V i) :=
  fun i ↦ cwThreeCanonicalBasis K 5 i

theorem monom_basis {K : Type u} [Field K] (a b c : Fin 7) :
    CWMonom K 5 a b c = (Basis.piTensorProduct (cb K)) ![a, b, c] := by
  rw [Basis.piTensorProduct_apply]
  unfold CWMonom
  congr 1
  funext i
  fin_cases i <;> dsimp only [cb, cwThreeCanonicalBasis]
  · exact (Pi.basisFun_apply K (Fin 7) a).symm
  · exact (Pi.basisFun_apply K (Fin 7) b).symm
  · exact (Pi.basisFun_apply K (Fin 7) c).symm

theorem base_expansion {K : Type u} [Field K] :
    (CWObj K 5).t =
      (∑ k : Fin 5, (
        (Basis.piTensorProduct (cb K)) ![0, (⟨k.val+1,by omega⟩ : Fin 7), ⟨k.val+1,by omega⟩] +
        (Basis.piTensorProduct (cb K)) ![⟨k.val+1,by omega⟩, 0, ⟨k.val+1,by omega⟩] +
        (Basis.piTensorProduct (cb K)) ![⟨k.val+1,by omega⟩, ⟨k.val+1,by omega⟩, 0])) +
      (Basis.piTensorProduct (cb K)) ![0, 0, 6] +
      (Basis.piTensorProduct (cb K)) ![0, 6, 0] +
      (Basis.piTensorProduct (cb K)) ![6, 0, 0] := by
  simp only [← monom_basis]
  rfl

theorem cycle_tuple {I : Type*} (a b c : I) (x : Fin 3 → I) :
    (![a,b,c] = fun i ↦ x (cyclicPerm i)) ↔ ![c,a,b] = x := by
  simp [funext_iff, Fin.forall_fin_succ, cyclicPerm, and_comm, and_left_comm]

theorem swap_tuple {I : Type*} (a b c : I) (x : Fin 3 → I) :
    (![a,b,c] = fun i ↦ x (swapFirstTwoPerm i)) ↔ ![b,a,c] = x := by
  simp [funext_iff, Fin.forall_fin_succ, swapFirstTwoPerm, and_comm, and_left_comm]

theorem base_cycle (K : Type u) [Field K] :
    SymUnder (fun x ↦ (Basis.piTensorProduct (cb K)).repr (CWObj K 5).t x) cyclicPerm := by
  classical
  intro x
  have h := base_expansion (K := K)
  dsimp only
  generalize (Basis.piTensorProduct (cb K)) = BB at h ⊢
  rw [h]
  simp only [map_add, map_sum, Finsupp.finset_sum_apply, Finsupp.add_apply,
    Basis.repr_self, Finsupp.single_apply]
  simp only [cycle_tuple]
  simp only [Finset.sum_add_distrib]
  ring

theorem base_swap (K : Type u) [Field K] :
    SymUnder (fun x ↦ (Basis.piTensorProduct (cb K)).repr (CWObj K 5).t x) swapFirstTwoPerm := by
  classical
  intro x
  have h := base_expansion (K := K)
  dsimp only
  generalize (Basis.piTensorProduct (cb K)) = BB at h ⊢
  rw [h]
  simp only [map_add, map_sum, Finsupp.finset_sum_apply, Finsupp.add_apply,
    Basis.repr_self, Finsupp.single_apply]
  simp only [swap_tuple]
  simp only [Finset.sum_add_distrib]
  ring

theorem base_all (K : Type u) [Field K] (σ : Equiv.Perm (Fin 3)) :
    SymUnder (fun x ↦ (Basis.piTensorProduct (cb K)).repr (CWObj K 5).t x) σ :=
  SymUnder.all (base_cycle K) (base_swap K) σ

theorem base_sym (K : Type u) [Field K] (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → Fin 7) :
    (Basis.piTensorProduct (cb K)).repr (CWObj K 5).t (fun i ↦ x (σ i)) =
      (Basis.piTensorProduct (cb K)).repr (CWObj K 5).t x :=
  base_all K σ x

/-! ## The fourth power -/

/-- The lifted canonical basis of `CW_5^{⊗4}` used by `e9fa2224`. -/
noncomputable def fb (K : Type u) [Field K] (i : Fin 3) :
    Basis (ULift.{u} (CWFourth.Coordinate 5)) K ((cwFourthObj K 5).V i) :=
  (cwFourthCanonicalBasis K 5 i).reindex Equiv.ulift.symm

theorem sq_basis (K : Type u) [Field K] (i : Fin 3) :
    cwSquareCanonicalBasis K 5 i =
      Module.Basis.tensorProduct (cb K i) (cb K i) := by
  fin_cases i <;> rfl

theorem sq_repr (K : Type u) [Field K] (a b : Fin 3 → Fin 7) :
    (Basis.piTensorProduct (fun i ↦ cwSquareCanonicalBasis K 5 i)).repr
        (TensorObj.kron (CWObj K 5) (CWObj K 5)).t (fun i ↦ (a i, b i)) =
      (Basis.piTensorProduct (cb K)).repr (CWObj K 5).t a *
        (Basis.piTensorProduct (cb K)).repr (CWObj K 5).t b := by
  have h : (fun i ↦ cwSquareCanonicalBasis K 5 i) =
      fun i ↦ Module.Basis.tensorProduct (cb K i) (cb K i) := funext (sq_basis K)
  rw [h]
  unfold TensorObj.kron
  rw [interchange_basis_repr_explicit]

theorem fourth_basis (K : Type u) [Field K] :
    cwFourthCanonicalBasis K 5 = fun i ↦ Module.Basis.tensorProduct
      (Module.Basis.tensorProduct (cb K i) (cb K i))
      (Module.Basis.tensorProduct (cb K i) (cb K i)) := by
  funext i
  rw [← sq_basis]
  rfl

theorem fourth_repr (K : Type u) [Field K] (y : Fin 3 → ULift.{u} (CWFourth.Coordinate 5)) :
    (Basis.piTensorProduct (fb K)).repr (cwFourthObj K 5).t y =
      ((Basis.piTensorProduct (cb K)).repr (CWObj K 5).t (fun i ↦ (y i).down.1.1) *
        (Basis.piTensorProduct (cb K)).repr (CWObj K 5).t (fun i ↦ (y i).down.1.2)) *
      ((Basis.piTensorProduct (cb K)).repr (CWObj K 5).t (fun i ↦ (y i).down.2.1) *
        (Basis.piTensorProduct (cb K)).repr (CWObj K 5).t (fun i ↦ (y i).down.2.2)) := by
  unfold fb
  rw [piTensorProduct_basis_reindex_explicit, Module.Basis.repr_reindex_apply]
  rw [show (Equiv.piCongrRight fun _ : Fin 3 ↦
      (Equiv.ulift.{u, 0} (α := CWFourth.Coordinate 5)).symm).symm y =
      fun i ↦ (((y i).down.1.1, (y i).down.1.2), ((y i).down.2.1, (y i).down.2.2)) from rfl]
  rw [fourth_basis]
  unfold cwFourthObj TensorObj.kron
  rw [interchange_basis_repr_explicit, interchange_basis_repr_explicit,
    interchange_basis_repr_explicit]

theorem fourth_all (K : Type u) [Field K] (σ : Equiv.Perm (Fin 3)) :
    SymUnder (fun y ↦ (Basis.piTensorProduct (fb K)).repr (cwFourthObj K 5).t y) σ := by
  intro y
  simp only [fourth_repr]
  rw [base_sym K σ (fun i ↦ (y i).down.1.1), base_sym K σ (fun i ↦ (y i).down.1.2),
    base_sym K σ (fun i ↦ (y i).down.2.1), base_sym K σ (fun i ↦ (y i).down.2.2)]

/-- The coefficient symmetry `mme_basis_projected_mode_permutation_iso` needs, for every
power of `CW_5^{⊗4}` in its word basis and every mode permutation. -/
theorem fourth_power_symmetric (K : Type u) [Field K] (n : ℕ) (σ : Equiv.Perm (Fin 3))
    (x : Fin 3 → Fin n → ULift.{u} (CWFourth.Coordinate 5)) :
    (Basis.piTensorProduct (fun i ↦ kronPowModeWordBasis (cwFourthObj K 5) i (fb K i) n)).repr
        ((cwFourthObj K 5).kronPow n).t (fun i ↦ x (σ i)) =
      (Basis.piTensorProduct (fun i ↦ kronPowModeWordBasis (cwFourthObj K 5) i (fb K i) n)).repr
        ((cwFourthObj K 5).kronPow n).t x := by
  change (powerBasis (cwFourthObj K 5) (fb K) n).repr _ _ =
    (powerBasis (cwFourthObj K 5) (fb K) n).repr _ _
  rw [power_coefficient_product, power_coefficient_product]
  exact Finset.prod_congr rfl (fun r _ ↦ fourth_all K σ (fun i ↦ x i r))

end MME.DWZFourthSymmetry

open MME.DWZFourthSymmetry CompleteSplit.CWFourth

theorem solution (K : Type u) [Field K] (n : ℕ)
    (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → Fin n → ULift.{u} (Coordinate 5)) :
    (Basis.piTensorProduct (fun i ↦ kronPowModeWordBasis (cwFourthObj K 5) i
        ((cwFourthCanonicalBasis K 5 i).reindex Equiv.ulift.symm) n)).repr
        ((cwFourthObj K 5).kronPow n).t (fun i ↦ x (σ i)) =
      (Basis.piTensorProduct (fun i ↦ kronPowModeWordBasis (cwFourthObj K 5) i
        ((cwFourthCanonicalBasis K 5 i).reindex Equiv.ulift.symm) n)).repr
        ((cwFourthObj K 5).kronPow n).t x :=
  fourth_power_symmetric K n σ x
