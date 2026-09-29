-- Prove2me | solution 1 for mme_kron_power_position_permutation_basis_transport
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:34:14.615689+00:00
-- url     : https://prove2.me/submissions/950aad1a-ccbd-4876-80e4-2a99dd3f6c11

import Definitions.Def_mme_kron_pow_mode_word_basis
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

private def wordOfFn {α : Type u} : (n : ℕ) → (Fin n → α) → PowIndex α n
  | 0, _ => PUnit.unit
  | n + 1, f => (f 0, wordOfFn n (fun r => f r.succ))

private theorem get_wordOfFn {α : Type u} (n : ℕ) (f : Fin n → α) :
    PowIndex.get n (wordOfFn n f) = f := by
  induction n with
  | zero => exact funext fun r => r.elim0
  | succ n ih =>
    funext r
    refine Fin.cases ?_ (fun r => ?_) r
    · rfl
    · exact congrFun (ih (fun r => f r.succ)) r

private theorem wordOfFn_get {α : Type u} (n : ℕ) (w : PowIndex α n) :
    wordOfFn n (PowIndex.get n w) = w := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change (w.1, wordOfFn n (PowIndex.get n w.2)) = w
    rw [ih]
    rfl

private def wordFnEquiv (α : Type u) (n : ℕ) : PowIndex α n ≃ (Fin n → α) where
  toFun := PowIndex.get n
  invFun := wordOfFn n
  left_inv := wordOfFn_get n
  right_inv := get_wordOfFn n

private def wordPerm (α : Type u) {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (PowIndex α n) :=
  (wordFnEquiv α n).trans ((Equiv.arrowCongr e (Equiv.refl α)).trans
    (wordFnEquiv α n).symm)

private theorem wordPerm_get {α : Type u} {n : ℕ} (e : Equiv.Perm (Fin n))
    (w : PowIndex α n) (r : Fin n) :
    PowIndex.get n (wordPerm α e w) r = PowIndex.get n w (e.symm r) := by
  change PowIndex.get n (wordOfFn n _) r = _
  rw [get_wordOfFn]
  rfl

private theorem interchange_tprod {K : Type u} [Field K]
    {V W : Fin 3 → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) = tprod K (fun i => v i ⊗ₜ[K] w i) := by
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem interchange_coeff {K : Type u} [Field K]
    {V W : Fin 3 → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {α β : Fin 3 → Type u}
    (b : ∀ i, Basis (α i) K (V i)) (c : ∀ i, Basis (β i) K (W i))
    (x : PiTensorProduct K V) (y : PiTensorProduct K W) (w : ∀ i, α i × β i) :
    (Basis.piTensorProduct (fun i => (b i).tensorProduct (c i))).repr
        (interchange x y) w =
      (Basis.piTensorProduct b).repr x (fun i => (w i).1) *
        (Basis.piTensorProduct c).repr y (fun i => (w i).2) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod d z =>
      simp only [map_smul, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul,
        interchange_tprod, Basis.piTensorProduct_repr_tprod_apply]
      have hc (i : Fin 3) : ((b i).tensorProduct (c i)).repr (v i ⊗ₜ[K] z i) (w i) =
          (c i).repr (z i) (w i).2 * (b i).repr (v i) (w i).1 := by
        rcases w i with ⟨j, k⟩
        exact Basis.tensorProduct_repr_tmul_apply (b i) (c i) (v i) (z i) j k
      simp only [hc, Finset.prod_mul_distrib]
      ring
    | add y z hy hz =>
      simp only [map_add, Finsupp.add_apply, hy, hz, mul_add]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, hx, hy, add_mul]

private theorem power_coeff {K : Type u} [Field K]
    (T : TensorObj K 3) {α : Fin 3 → Type u} (b : ∀ i, Basis (α i) K (T.V i))
    (n : ℕ) (w : ∀ i, PowIndex (α i) n) :
    (Basis.piTensorProduct (fun i => kronPowModeBasis T i (b i) n)).repr
        (T.kronPow n).t w =
      ∏ r : Fin n, (Basis.piTensorProduct b).repr T.t
        (fun i => PowIndex.get n (w i) r) := by
  induction n with
  | zero =>
    change (Basis.piTensorProduct (fun i => Basis.singleton (PowIndex (α i) 0) K)).repr
      (tprod K (fun _ : Fin 3 => (1 : K))) w = _
    rw [Basis.piTensorProduct_repr_tprod_apply]
    simp only [Basis.singleton_repr, Finset.prod_const_one, Finset.univ_eq_empty,
      Finset.prod_empty]
  | succ n ih =>
    change (Basis.piTensorProduct (fun i => (b i).tensorProduct
      (kronPowModeBasis T i (b i) n))).repr (interchange T.t (T.kronPow n).t) w = _
    rw [interchange_coeff, ih, Fin.prod_univ_succ]
    rfl

/-- Permuting the positions of a tensor power preserves its tensor and applies
that same permutation to every mode's numeric word coordinates. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    {α : Fin 3 → Type u} (b : ∀ i, Basis (α i) K (T.V i))
    (n : ℕ) (e : Equiv.Perm (Fin n)) :
    ∃ F : ∀ i, (T.kronPow n).V i ≃ₗ[K] (T.kronPow n).V i,
      PiTensorProduct.map (fun i => (F i).toLinearMap) (T.kronPow n).t =
        (T.kronPow n).t ∧
      ∀ i, ∃ perm : Equiv.Perm (PowIndex (α i) n),
        (∀ w, F i (kronPowModeBasis T i (b i) n w) =
          kronPowModeBasis T i (b i) n (perm w)) ∧
        (∀ w r, PowIndex.get n (perm w) r = PowIndex.get n w (e.symm r)) := by
  classical
  letI (i : Fin 3) : Finite (α i) := Module.Finite.finite_basis (b i)
  letI (i : Fin 3) : Fintype (α i) := Fintype.ofFinite _
  let B := fun i => kronPowModeBasis T i (b i) n
  let F := fun i => (B i).equiv (B i) (wordPerm (α i) e)
  let C := Basis.piTensorProduct B
  let E : Equiv.Perm (∀ i, PowIndex (α i) n) :=
    Equiv.piCongrRight (fun i => wordPerm (α i) e)
  have hB (w : ∀ i, PowIndex (α i) n) :
      PiTensorProduct.map (fun i => (F i).toLinearMap) (C w) = C (E w) := by
    change PiTensorProduct.map (fun i => (F i).toLinearMap)
      (Basis.piTensorProduct B w) = Basis.piTensorProduct B (E w)
    rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, Basis.piTensorProduct_apply]
    congr 1
    funext i
    exact Basis.equiv_apply _ _ _ _
  have hc (w : ∀ i, PowIndex (α i) n) :
      C.repr (T.kronPow n).t (E w) = C.repr (T.kronPow n).t w := by
    change (Basis.piTensorProduct (fun i => kronPowModeBasis T i (b i) n)).repr
      (T.kronPow n).t (fun i => wordPerm (α i) e (w i)) = _
    rw [power_coeff, power_coeff]
    simp only [wordPerm_get]
    exact Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  refine ⟨F, ?_, ?_⟩
  · calc
      PiTensorProduct.map (fun i => (F i).toLinearMap) (T.kronPow n).t =
          ∑ w, C.repr (T.kronPow n).t w • C (E w) := by
            conv_lhs => rw [← C.sum_repr (T.kronPow n).t]
            simp only [map_sum, map_smul, hB]
      _ = ∑ w, C.repr (T.kronPow n).t (E w) • C (E w) := by
        simp only [hc]
      _ = (T.kronPow n).t := by
        calc
          _ = ∑ w, C.repr (T.kronPow n).t w • C w :=
            Fintype.sum_equiv E _ _ (fun _ => rfl)
          _ = _ := C.sum_repr _
  · intro i
    exact ⟨wordPerm (α i) e, fun w => Basis.equiv_apply _ _ _ _, wordPerm_get e⟩

#print axioms solution
