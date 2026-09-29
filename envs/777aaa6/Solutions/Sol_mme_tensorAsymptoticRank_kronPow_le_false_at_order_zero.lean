-- Prove2me | solution 1 for mme_tensorAsymptoticRank_kronPow_le_false_at_order_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:34:34.900423+00:00
-- url     : https://prove2.me/submissions/5911a9cd-44cc-4525-864f-f393cbdc22b1

import Definitions.Def_mme_tensor_rank

open MME PiTensorProduct BigOperators

universe u


namespace CWKronPowCounterexample

noncomputable section

private theorem interchange_tprod
    {K : Type u} [Field K] {V W : Fin 0 → Type u}
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

private theorem empty_map_value
    {K : Type u} [Field K] {V W : Fin 0 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (x : PiTensorProduct K V) :
    PiTensorProduct.isEmptyEquiv (Fin 0) (PiTensorProduct.map f x) =
      PiTensorProduct.isEmptyEquiv (Fin 0) x := by
  conv_lhs =>
    rw [← (PiTensorProduct.isEmptyEquiv (Fin 0)).symm_apply_apply x]
  rw [PiTensorProduct.isEmptyEquiv_symm_apply]
  simp only [map_smul, PiTensorProduct.map_tprod,
    PiTensorProduct.isEmptyEquiv_apply_tprod]
  simp

private theorem empty_interchange_value
    {K : Type u} [Field K] {V W : Fin 0 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (y : PiTensorProduct K W) :
    PiTensorProduct.isEmptyEquiv (Fin 0) (interchange x y) =
      PiTensorProduct.isEmptyEquiv (Fin 0) x *
        PiTensorProduct.isEmptyEquiv (Fin 0) y := by
  conv_lhs =>
    rw [← (PiTensorProduct.isEmptyEquiv (Fin 0)).symm_apply_apply x]
    rw [← (PiTensorProduct.isEmptyEquiv (Fin 0)).symm_apply_apply y]
  rw [PiTensorProduct.isEmptyEquiv_symm_apply,
    PiTensorProduct.isEmptyEquiv_symm_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [interchange_tprod, PiTensorProduct.isEmptyEquiv_apply_tprod]
  simp [mul_comm]

def scalarObj (c : ℚ) : TensorObj ℚ 0 where
  V := fun _ => ℚ
  t := (PiTensorProduct.isEmptyEquiv (Fin 0)).symm c

def scalarValue (X : TensorObj ℚ 0) : ℚ :=
  PiTensorProduct.isEmptyEquiv (Fin 0) X.t

@[simp] theorem scalarValue_scalarObj (c : ℚ) : scalarValue (scalarObj c) = c := by
  exact (PiTensorProduct.isEmptyEquiv (Fin 0)).apply_symm_apply c

theorem scalarValue_kron (X Y : TensorObj ℚ 0) :
    scalarValue (TensorObj.kron X Y) = scalarValue X * scalarValue Y := by
  exact empty_interchange_value X.t Y.t

theorem scalarValue_kronPow (X : TensorObj ℚ 0) (n : ℕ) :
    scalarValue (X.kronPow n) = scalarValue X ^ n := by
  induction n with
  | zero =>
      simp only [TensorObj.kronPow, pow_zero]
      unfold scalarValue TensorObj.oneObj
      exact PiTensorProduct.isEmptyEquiv_apply_tprod
        (R := ℚ) (s := fun _ : Fin 0 => ℚ) (Fin 0) (fun _ => (1 : ℚ))
  | succ n ih =>
      simp only [TensorObj.kronPow, scalarValue_kron, ih]
      rw [pow_succ', mul_comm]

theorem restrict_iff_scalarValue (X Y : TensorObj ℚ 0) :
    TensorObj.Restrict X Y ↔ scalarValue X = scalarValue Y := by
  constructor
  · rintro ⟨f, hf⟩
    unfold scalarValue
    rw [← hf, empty_map_value]
  · intro h
    refine ⟨(fun i => Fin.elim0 i), ?_⟩
    apply (PiTensorProduct.isEmptyEquiv (Fin 0)).injective
    rw [empty_map_value]
    exact h.symm

@[simp] theorem scalarValue_diagObj (r : ℕ) :
    scalarValue (TensorObj.diagObj ℚ 0 r) = r := by
  unfold scalarValue TensorObj.diagObj
  rw [map_sum]
  simp only [PiTensorProduct.isEmptyEquiv_apply_tprod]
  simp

theorem tensorRankObj_eq_scalarFiber (X : TensorObj ℚ 0) :
    tensorRankObj X = sInf {r : ℕ | (r : ℚ) = scalarValue X} := by
  unfold tensorRankObj
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, restrict_iff_scalarValue, scalarValue_diagObj]
  exact eq_comm

@[simp] theorem tensorRankObj_scalarObj_neg_one :
    tensorRankObj (scalarObj (-1)) = 0 := by
  rw [tensorRankObj_eq_scalarFiber]
  have hset : {r : ℕ | (r : ℚ) = scalarValue (scalarObj (-1))} = ∅ := by
    ext r
    simp only [Set.mem_setOf_eq, scalarValue_scalarObj, Set.mem_empty_iff_false, iff_false]
    have hr : (0 : ℚ) ≤ r := by positivity
    intro h
    linarith
  rw [hset]
  exact Nat.sInf_empty

@[simp] theorem tensorRankObj_scalarObj_one :
    tensorRankObj (scalarObj 1) = 1 := by
  rw [tensorRankObj_eq_scalarFiber]
  have hset : {r : ℕ | (r : ℚ) = scalarValue (scalarObj 1)} = {1} := by
    ext r
    simp
  rw [hset]
  exact csInf_singleton 1

theorem tensorRankObj_eq_zero_of_scalarValue_neg_one
    (X : TensorObj ℚ 0) (hX : scalarValue X = -1) :
    tensorRankObj X = 0 := by
  rw [tensorRankObj_eq_scalarFiber, hX]
  simpa only [tensorRankObj_eq_scalarFiber, scalarValue_scalarObj] using
    tensorRankObj_scalarObj_neg_one

theorem tensorRankObj_eq_one_of_scalarValue_one
    (X : TensorObj ℚ 0) (hX : scalarValue X = 1) :
    tensorRankObj X = 1 := by
  rw [tensorRankObj_eq_scalarFiber, hX]
  simpa only [tensorRankObj_eq_scalarFiber, scalarValue_scalarObj] using
    tensorRankObj_scalarObj_one

@[simp] theorem tensorRankObj_neg_one_kronPow_one :
    tensorRankObj ((scalarObj (-1)).kronPow 1) = 0 := by
  apply tensorRankObj_eq_zero_of_scalarValue_neg_one
  rw [scalarValue_kronPow, scalarValue_scalarObj]
  norm_num

@[simp] theorem tensorRankObj_neg_one_square_kronPow (n : ℕ) :
    tensorRankObj (((scalarObj (-1)).kronPow 2).kronPow (n + 1)) = 1 := by
  apply tensorRankObj_eq_one_of_scalarValue_one
  rw [scalarValue_kronPow, scalarValue_kronPow, scalarValue_scalarObj]
  norm_num

@[simp] theorem tensorAsymptoticRank_scalarObj_neg_one :
    tensorAsymptoticRank (scalarObj (-1)) = 0 := by
  rw [tensorAsymptoticRank]
  let a : ℕ → ℝ := fun n =>
    (tensorRankObj ((scalarObj (-1)).kronPow (n + 1)) : ℝ) ^
      ((1 : ℝ) / (n + 1))
  have hbdd : BddBelow (Set.range a) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  apply le_antisymm
  · calc
      (⨅ n : ℕ, a n) ≤ a 0 := ciInf_le hbdd 0
      _ = 0 := by simp [a]
  · apply le_ciInf
    intro n
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

@[simp] theorem tensorAsymptoticRank_neg_one_square :
    tensorAsymptoticRank ((scalarObj (-1)).kronPow 2) = 1 := by
  rw [tensorAsymptoticRank]
  simp

/-- A concrete order-zero counterexample to the unrestricted Kronecker-power bound. -/
theorem false_unrestricted_kronPow_bound :
    ∃ X : TensorObj ℚ 0,
      ¬ tensorAsymptoticRank (X.kronPow 2) ≤ tensorAsymptoticRank X ^ 2 := by
  refine ⟨scalarObj (-1), ?_⟩
  simp

end

end CWKronPowCounterexample


theorem solution :
    ∃ X : TensorObj ℚ 0,
      ¬ tensorAsymptoticRank (X.kronPow 2) ≤ tensorAsymptoticRank X ^ 2 :=
  CWKronPowCounterexample.false_unrestricted_kronPow_bound
