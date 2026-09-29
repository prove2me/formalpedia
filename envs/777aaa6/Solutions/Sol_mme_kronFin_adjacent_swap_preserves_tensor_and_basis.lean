-- Prove2me | solution 1 for mme_kronFin_adjacent_swap_preserves_tensor_and_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T19:49:36.986449+00:00
-- url     : https://prove2.me/submissions/2b455a63-8035-40c6-8f39-4ebf45078732

import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_kronFin_adjacent_swap_data
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_kronFin_mode_pi_basis
import Mathlib.GroupTheory.Perm.Sign

open MME PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.TensorObj

/-- `interchange` evaluated on two pure tensors. -/
theorem mme_interchange_tprod
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- The modewise tensor commutor exchanges the two inputs of `interchange`. -/
theorem mme_interchange_comm
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W) :
    PiTensorProduct.map
        (fun i => (TensorProduct.comm K (W i) (V i)).toLinearMap)
        (interchange b a) =
      interchange a b := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod c' w =>
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      rw [mme_interchange_tprod, PiTensorProduct.map_tprod,
        mme_interchange_tprod, mul_comm c c']
      congr 2
    | add x y ih1 ih2 =>
      simp only [map_add, LinearMap.add_apply, ih1, ih2]
  | add x y ih1 ih2 =>
    simp only [LinearMap.add_apply, map_add, ih1, ih2]

/-- The modewise tensor associator reassociates three inputs of
`interchange`. -/
theorem mme_interchange_assoc
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W U : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W)
    (c : PiTensorProduct K U) :
    PiTensorProduct.map
        (fun i =>
          (TensorProduct.assoc K (V i) (W i) (U i)).toLinearMap)
        (interchange (interchange a b) c) =
      interchange a (interchange b c) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod ca v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod cb w =>
      induction c using PiTensorProduct.induction_on with
      | smul_tprod cc x =>
        simp only [map_smul, LinearMap.smul_apply, smul_smul]
        rw [mme_interchange_tprod, mme_interchange_tprod,
          PiTensorProduct.map_tprod, mme_interchange_tprod,
          mme_interchange_tprod,
          show cc * (cb * ca) = cc * cb * ca by ring]
        congr 1
      | add x y ih1 ih2 => simp only [map_add, ih1, ih2]
    | add x y ih1 ih2 =>
      simp only [map_add, LinearMap.add_apply, ih1, ih2]
  | add x y ih1 ih2 =>
    simp only [LinearMap.add_apply, map_add, ih1, ih2]

/-- The inverse modewise associator turns a right-associated interchange into
a left-associated one. -/
theorem mme_interchange_assoc_symm
    {K : Type u} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W U : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W)
    (c : PiTensorProduct K U) :
    PiTensorProduct.map
        (fun i =>
          (TensorProduct.assoc K (V i) (W i) (U i)).symm.toLinearMap)
        (interchange a (interchange b c)) =
      interchange (interchange a b) c := by
  rw [← mme_interchange_assoc a b c]
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have hcomp :
      (fun i =>
          (TensorProduct.assoc K (V i) (W i) (U i)).symm.toLinearMap ∘ₗ
            (TensorProduct.assoc K (V i) (W i) (U i)).toLinearMap) =
        (fun _ => LinearMap.id) := by
    funext i
    ext z
    simp
  rw [hcomp, PiTensorProduct.map_id]
  rfl

/-- The family obtained by exchanging the first two entries. -/
def kronFinFrontSwapFamily
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) : Fin (n + 2) → TensorObj K d :=
  Fin.cases (T 1) (Fin.cases (T 0) (fun r ↦ T r.succ.succ))

/-- The correspondingly exchanged dependent index family. -/
def kronFinFrontSwapIndex {n : ℕ}
    (index : Fin (n + 2) → Type u) : Fin (n + 2) → Type u :=
  Fin.cases (index 1) (Fin.cases (index 0) (fun r ↦ index r.succ.succ))

/-- Exchange the first two entries of a dependent word back into the target
order. -/
def kronFinFrontUnswapWord {n : ℕ}
    {index : Fin (n + 2) → Type u}
    (w : ∀ r, kronFinFrontSwapIndex index r) : ∀ r, index r :=
  Fin.cases (w 1) (Fin.cases (w 0) (fun r ↦ w r.succ.succ))

/-- The factor bases attached to the exchanged family. -/
noncomputable def kronFinFrontSwapBasis
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (i : Fin d)
    {index : Fin (n + 2) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i)) :
    ∀ r, Basis (kronFinFrontSwapIndex index r) K
      (((kronFinFrontSwapFamily T) r).V i) :=
  Fin.cases (b 1) (Fin.cases (b 0) (fun r ↦ b r.succ.succ))

/-- The mode equivalence which exchanges the first two factors of a
right-associated ordered Kronecker product. -/
noncomputable def kronFinFrontSwapModeEquiv
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (i : Fin d) :
    (TensorObj.kronFin (n + 2) (kronFinFrontSwapFamily T)).V i ≃ₗ[K]
      (TensorObj.kronFin (n + 2) T).V i := by
  let R := (TensorObj.kronFin n (fun r : Fin n ↦ T r.succ.succ)).V i
  let E :
      (T 1).V i ⊗[K] ((T 0).V i ⊗[K] R) ≃ₗ[K]
        (T 0).V i ⊗[K] ((T 1).V i ⊗[K] R) :=
    ((TensorProduct.assoc K ((T 1).V i) ((T 0).V i) R).symm).trans
      ((TensorProduct.congr
          (TensorProduct.comm K ((T 1).V i) ((T 0).V i))
          (LinearEquiv.refl K R)).trans
        (TensorProduct.assoc K ((T 0).V i) ((T 1).V i) R))
  exact E

/-- Exchanging the first two factors through the canonical associator and
commutor sends the literal ordered Kronecker tensor to the original one. -/
theorem kronFinFrontSwapModeEquiv_preserves_tensor
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) :
    PiTensorProduct.map
        (fun i => (kronFinFrontSwapModeEquiv T i).toLinearMap)
        (TensorObj.kronFin (n + 2)
          (kronFinFrontSwapFamily T)).t =
      (TensorObj.kronFin (n + 2) T).t := by
  let R := TensorObj.kronFin n (fun r : Fin n ↦ T r.succ.succ)
  have hF :
      (fun i => (kronFinFrontSwapModeEquiv T i).toLinearMap) =
        fun i =>
          (TensorProduct.assoc K ((T 0).V i) ((T 1).V i) (R.V i)).toLinearMap ∘ₗ
            (TensorProduct.map
              (TensorProduct.comm K ((T 1).V i) ((T 0).V i)).toLinearMap
              (LinearMap.id : R.V i →ₗ[K] R.V i)) ∘ₗ
            (TensorProduct.assoc K
              ((T 1).V i) ((T 0).V i) (R.V i)).symm.toLinearMap := by
    funext i
    ext x
    rfl
  rw [hF]
  change PiTensorProduct.map _
      (interchange (T 1).t (interchange (T 0).t R.t)) =
    interchange (T 0).t (interchange (T 1).t R.t)
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply,
    PiTensorProduct.map_comp, LinearMap.comp_apply]
  rw [mme_interchange_assoc_symm]
  rw [TensorObj.TypeGrading.kronMap_interchange]
  rw [mme_interchange_comm, PiTensorProduct.map_id]
  exact mme_interchange_assoc (T 0).t (T 1).t R.t

/-- The recursive product basis evaluates as the head basis vector tensored
with the product basis of the tail. -/
theorem kronFinModePiBasis_succ_apply
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 1) → TensorObj K d) (i : Fin d)
    {index : Fin (n + 1) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i))
    (w : ∀ r, index r) :
    TensorObj.kronFinModePiBasis (n + 1) T i b w =
      (b 0 (w 0)) ⊗ₜ[K]
        (TensorObj.kronFinModePiBasis n
          (fun r : Fin n ↦ T r.succ) i
          (fun r ↦ b r.succ) (fun r ↦ w r.succ)) := by
  change (((b 0).tensorProduct
    (TensorObj.kronFinModePiBasis n
      (fun r : Fin n ↦ T r.succ) i
      (fun r ↦ b r.succ))).reindex (Fin.consEquiv index)) w = _
  rw [Module.Basis.reindex_apply, Fin.consEquiv_symm_apply,
    Module.Basis.tensorProduct_apply]
  rfl

/-- The front-swap mode equivalence has the literal expected action on the
function-indexed product basis. -/
theorem kronFinFrontSwapModeEquiv_basis
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (i : Fin d)
    {index : Fin (n + 2) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i))
    (w : ∀ r, kronFinFrontSwapIndex index r) :
    kronFinFrontSwapModeEquiv T i
        (TensorObj.kronFinModePiBasis (n + 2)
          (kronFinFrontSwapFamily T) i
          (kronFinFrontSwapBasis T i b) w) =
      TensorObj.kronFinModePiBasis (n + 2) T i b
        (kronFinFrontUnswapWord w) := by
  simp only [kronFinModePiBasis_succ_apply]
  simp only [kronFinFrontSwapFamily, kronFinFrontSwapBasis,
    kronFinFrontSwapIndex, kronFinFrontUnswapWord, Fin.cases_zero,
    Fin.cases_succ]
  let z := TensorObj.kronFinModePiBasis n
    (fun r : Fin n ↦ T r.succ.succ) i
    (fun r ↦ b r.succ.succ) (fun r ↦ w r.succ.succ)
  change (TensorProduct.assoc K ((T 0).V i) ((T 1).V i)
      ((TensorObj.kronFin n (fun r : Fin n ↦ T r.succ.succ)).V i))
      ((TensorProduct.congr
        (TensorProduct.comm K ((T 1).V i) ((T 0).V i))
        (LinearEquiv.refl K
          ((TensorObj.kronFin n
            (fun r : Fin n ↦ T r.succ.succ)).V i)))
        ((TensorProduct.assoc K ((T 1).V i) ((T 0).V i)
          ((TensorObj.kronFin n
            (fun r : Fin n ↦ T r.succ.succ)).V i)).symm
          ((b 1 (w 0)) ⊗ₜ[K] ((b 0 (w 1)) ⊗ₜ[K] z)))) =
    (b 0 (w 1)) ⊗ₜ[K] ((b 1 (w 0)) ⊗ₜ[K] z)
  rw [TensorProduct.assoc_symm_tmul, TensorProduct.congr_tmul,
    TensorProduct.comm_tmul, LinearEquiv.refl_apply,
    TensorProduct.assoc_tmul]


/-- Canonical mode equivalence for exchanging any two adjacent factors of a
right-associated ordered Kronecker product. -/
noncomputable def kronFinAdjacentSwapModeEquiv
    {K : Type u} [Field K] {d : ℕ} :
    ∀ {n : ℕ} (T : Fin (n + 2) → TensorObj K d)
      (j : Fin (n + 1)) (i : Fin d),
      (TensorObj.kronFin (n + 2)
        (kronFinAdjacentSwapFamily T j)).V i ≃ₗ[K]
        (TensorObj.kronFin (n + 2) T).V i
  | 0, T, _, i => kronFinFrontSwapModeEquiv T i
  | n + 1, T, j, i => by
      refine Fin.cases (kronFinFrontSwapModeEquiv T i) (fun q ↦ ?_) j
      · let tail : Fin (n + 2) → TensorObj K d := fun r ↦ T r.succ
        exact TensorProduct.congr
          (LinearEquiv.refl K ((T 0).V i))
          (kronFinAdjacentSwapModeEquiv tail q i)

/-- One-step reduction of an adjacent swap strictly inside the tail. -/
theorem kronFinAdjacentSwapFamily_succ
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 3) → TensorObj K d) (q : Fin (n + 1)) :
    kronFinAdjacentSwapFamily T q.succ =
      Fin.cons (T 0)
        (kronFinAdjacentSwapFamily
          (fun r : Fin (n + 2) ↦ T r.succ) q) := by
  rfl

/-- Pointwise tail form of `kronFinAdjacentSwapFamily_succ`. -/
theorem kronFinAdjacentSwapFamily_succ_apply_tail
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 3) → TensorObj K d) (q : Fin (n + 1))
    (r : Fin (n + 2)) :
    kronFinAdjacentSwapFamily T q.succ r.succ =
      kronFinAdjacentSwapFamily
        (fun s : Fin (n + 2) ↦ T s.succ) q r := by
  rfl

/-- One-step reduction of the mode equivalence for an adjacent swap strictly
inside the tail. -/
theorem kronFinAdjacentSwapModeEquiv_succ
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 3) → TensorObj K d) (q : Fin (n + 1)) (i : Fin d) :
    kronFinAdjacentSwapModeEquiv T q.succ i =
      TensorProduct.congr (LinearEquiv.refl K ((T 0).V i))
        (kronFinAdjacentSwapModeEquiv
          (fun r : Fin (n + 2) ↦ T r.succ) q i) := by
  rfl

/-- Recursive reduction of the dependent index family for an adjacent swap
strictly inside the tail. -/
theorem kronFinAdjacentSwapIndex_succ
    {n : ℕ} (index : Fin (n + 3) → Type u) (q : Fin (n + 1)) :
    kronFinAdjacentSwapIndex index q.succ =
      Fin.cons (index 0)
        (kronFinAdjacentSwapIndex
          (fun r : Fin (n + 2) ↦ index r.succ) q) := by
  rfl

/-- Recursive reduction of the factor bases for an adjacent swap strictly
inside the tail. -/
theorem kronFinAdjacentSwapBasis_succ
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 3) → TensorObj K d) (q : Fin (n + 1)) (i : Fin d)
    {index : Fin (n + 3) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i)) :
    kronFinAdjacentSwapBasis T q.succ i b =
      Fin.cons (b 0)
        (kronFinAdjacentSwapBasis
          (fun r : Fin (n + 2) ↦ T r.succ) q i
          (fun r ↦ b r.succ)) := by
  rfl

/-- The head coordinate is unchanged when an adjacent swap lies strictly in
the tail. -/
theorem kronFinAdjacentUnswapWord_succ_zero
    {n : ℕ} {index : Fin (n + 3) → Type u} (q : Fin (n + 1))
    (w : ∀ r, kronFinAdjacentSwapIndex index q.succ r) :
    kronFinAdjacentUnswapWord q.succ w 0 = w 0 := by
  rfl

/-- Tail coordinates are recursively restored when an adjacent swap lies
strictly in the tail. -/
theorem kronFinAdjacentUnswapWord_succ_tail
    {n : ℕ} {index : Fin (n + 3) → Type u} (q : Fin (n + 1))
    (w : ∀ r, kronFinAdjacentSwapIndex index q.succ r)
    (r : Fin (n + 2)) :
    kronFinAdjacentUnswapWord q.succ w r.succ =
      kronFinAdjacentUnswapWord q (fun s : Fin (n + 2) ↦ w s.succ) r := by
  rfl

/-- Tensoring a tensor-preserving family of maps on the left with identity
again preserves the literal Kronecker tensor. -/
theorem kron_left_identity_lift_preserves_tensor
    {K : Type u} [Field K] {d : ℕ}
    (A B C : TensorObj K d)
    (f : ∀ i : Fin d, B.V i →ₗ[K] C.V i)
    (h : PiTensorProduct.map f B.t = C.t) :
    PiTensorProduct.map
        (fun i => TensorProduct.map
          (LinearMap.id : A.V i →ₗ[K] A.V i) (f i))
        (TensorObj.kron A B).t =
      (TensorObj.kron A C).t := by
  change PiTensorProduct.map _ (interchange A.t B.t) =
    interchange A.t C.t
  rw [TensorObj.TypeGrading.kronMap_interchange,
    PiTensorProduct.map_id, h]
  rfl

/-- Every recursively lifted adjacent swap sends the literal ordered
Kronecker tensor to the unswapped one. -/
theorem kronFinAdjacentSwapModeEquiv_preserves_tensor
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) :
    PiTensorProduct.map
        (fun i => (kronFinAdjacentSwapModeEquiv T j i).toLinearMap)
        (TensorObj.kronFin (n + 2)
          (kronFinAdjacentSwapFamily T j)).t =
      (TensorObj.kronFin (n + 2) T).t := by
  induction n with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst hj
      exact kronFinFrontSwapModeEquiv_preserves_tensor T
  | succ n ih =>
      refine Fin.cases ?_ (fun q ↦ ?_) j
      · exact kronFinFrontSwapModeEquiv_preserves_tensor T
      · let tail : Fin (n + 2) → TensorObj K d := fun r ↦ T r.succ
        exact kron_left_identity_lift_preserves_tensor
          (T 0)
          (TensorObj.kronFin (n + 2)
            (kronFinAdjacentSwapFamily tail q))
          (TensorObj.kronFin (n + 2) tail)
          (fun i =>
            (kronFinAdjacentSwapModeEquiv tail q i).toLinearMap)
          (ih tail q)

/-- Every recursively lifted adjacent swap has the expected literal action
on a heterogeneous function-indexed product basis. -/
theorem kronFinAdjacentSwapModeEquiv_basis
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) (i : Fin d)
    {index : Fin (n + 2) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i))
    (w : ∀ r, kronFinAdjacentSwapIndex index j r) :
    kronFinAdjacentSwapModeEquiv T j i
        (TensorObj.kronFinModePiBasis (n + 2)
          (kronFinAdjacentSwapFamily T j) i
          (kronFinAdjacentSwapBasis T j i b) w) =
      TensorObj.kronFinModePiBasis (n + 2) T i b
        (kronFinAdjacentUnswapWord j w) := by
  induction n with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst hj
      exact kronFinFrontSwapModeEquiv_basis T i b w
  | succ n ih =>
      revert w
      refine Fin.cases ?_ (fun q w ↦ ?_) j
      · intro w
        exact kronFinFrontSwapModeEquiv_basis T i b w
      · rw [kronFinAdjacentSwapModeEquiv_succ]
        rw [kronFinModePiBasis_succ_apply
          (kronFinAdjacentSwapFamily T q.succ) i
          (kronFinAdjacentSwapBasis T q.succ i b) w]
        rw [kronFinModePiBasis_succ_apply T i b
          (kronFinAdjacentUnswapWord q.succ w)]
        simp only [kronFinAdjacentSwapBasis_succ,
          Fin.cons_zero, Fin.cons_succ,
          kronFinAdjacentUnswapWord_succ_zero,
          kronFinAdjacentUnswapWord_succ_tail]
        change
          (TensorProduct.congr (LinearEquiv.refl K ((T 0).V i))
            (kronFinAdjacentSwapModeEquiv
              (fun r : Fin (n + 2) ↦ T r.succ) q i))
            ((b 0 (w 0)) ⊗ₜ[K]
              TensorObj.kronFinModePiBasis (n + 2)
                (kronFinAdjacentSwapFamily
                  (fun r : Fin (n + 2) ↦ T r.succ) q) i
                (kronFinAdjacentSwapBasis
                  (fun r : Fin (n + 2) ↦ T r.succ) q i
                  (fun r ↦ b r.succ))
                (fun r ↦ w r.succ)) =
            (b 0 (w 0)) ⊗ₜ[K]
              TensorObj.kronFinModePiBasis (n + 2)
                (fun r : Fin (n + 2) ↦ T r.succ) i
                (fun r ↦ b r.succ)
                (fun r ↦
                  kronFinAdjacentUnswapWord q
                    (fun s : Fin (n + 2) ↦ w s.succ) r)
        rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
        rw [ih (fun r : Fin (n + 2) ↦ T r.succ) q
          (fun r ↦ b r.succ) (fun r ↦ w r.succ)]


end MME.TensorObj

set_option warningAsError true

/-- Swapping any adjacent pair of heterogeneous factors is realized by
modewise linear equivalences which preserve the literal tensor and act
exactly on every dependent product basis word. -/
theorem solution
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) :
    ∃ F : ∀ i : Fin d,
        (TensorObj.kronFin (n + 2)
          (TensorObj.kronFinAdjacentSwapFamily T j)).V i ≃ₗ[K]
        (TensorObj.kronFin (n + 2) T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin (n + 2)
            (TensorObj.kronFinAdjacentSwapFamily T j)).t =
        (TensorObj.kronFin (n + 2) T).t ∧
      ∀ (i : Fin d) {index : Fin (n + 2) → Type u}
          (b : ∀ r, Basis (index r) K ((T r).V i))
          (w : ∀ r, TensorObj.kronFinAdjacentSwapIndex index j r),
        F i
            (TensorObj.kronFinModePiBasis (n + 2)
              (TensorObj.kronFinAdjacentSwapFamily T j) i
              (TensorObj.kronFinAdjacentSwapBasis T j i b) w) =
          TensorObj.kronFinModePiBasis (n + 2) T i b
            (TensorObj.kronFinAdjacentUnswapWord j w) := by
  exact ⟨fun i ↦ TensorObj.kronFinAdjacentSwapModeEquiv T j i,
    TensorObj.kronFinAdjacentSwapModeEquiv_preserves_tensor T j,
    fun i index b w ↦
      TensorObj.kronFinAdjacentSwapModeEquiv_basis T j i
        (index := index) b w⟩

