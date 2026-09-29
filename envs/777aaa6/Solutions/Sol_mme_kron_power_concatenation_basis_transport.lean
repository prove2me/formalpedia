-- Prove2me | solution 1 for mme_kron_power_concatenation_basis_transport
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:18:58.700607+00:00
-- url     : https://prove2.me/submissions/6231d44e-ef76-4b62-acf6-d9dbaaf55345

import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_TypeGrading_kron

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

private def appendWord {ι : Type u} (n : ℕ) :
    (m : ℕ) → PowIndex ι m → PowIndex ι n → PowIndex ι (n + m)
  | 0, _, v => v
  | m + 1, w, v => (w.1, appendWord n m w.2 v)

private def appendWordEquiv (ι : Type u) (n : ℕ) :
    (m : ℕ) → (PowIndex ι m × PowIndex ι n) ≃ PowIndex ι (n + m)
  | 0 => Equiv.punitProd _
  | m + 1 => (Equiv.prodAssoc _ _ _).trans
      (Equiv.prodCongr (Equiv.refl ι) (appendWordEquiv ι n m))

private theorem appendWordEquiv_apply {ι : Type u} (n m : ℕ)
    (w : PowIndex ι m) (v : PowIndex ι n) :
    appendWordEquiv ι n m (w, v) = appendWord n m w v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (w.1, appendWordEquiv ι n m (w.2, v)) = _
    rw [ih]
    rfl

private theorem appendWord_get_left {ι : Type u} (n m : ℕ)
    (w : PowIndex ι m) (v : PowIndex ι n) (r : Fin m) :
    PowIndex.get (n + m) (appendWord n m w v) ⟨r.val, by omega⟩ =
      PowIndex.get m w r := by
  induction m with
  | zero => exact r.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun r => ?_) r
    · rfl
    · change PowIndex.get (n + m) (appendWord n m w.2 v) ⟨r.val, by omega⟩ =
        PowIndex.get m w.2 r
      exact ih w.2 r

private theorem appendWord_get_right {ι : Type u} (n m : ℕ)
    (w : PowIndex ι m) (v : PowIndex ι n) (r : Fin n) :
    PowIndex.get (n + m) (appendWord n m w v) ⟨m + r.val, by omega⟩ =
      PowIndex.get n v r := by
  induction m with
  | zero =>
    have h : (⟨0 + r.val, by omega⟩ : Fin (n + 0)) = r := by ext; simp
    rw [h]
    rfl
  | succ m ih =>
    have h : (⟨m + 1 + r.val, by omega⟩ : Fin (n + (m + 1))) =
        (⟨m + r.val, by omega⟩ : Fin (n + m)).succ := by ext; simp; omega
    rw [h]
    change PowIndex.get (n + m) (appendWord n m w.2 v) _ = _
    exact ih w.2

private noncomputable def appendMode {K : Type u} [Field K]
    (T : TensorObj K 3) (n : ℕ) (i : Fin 3) :
    (m : ℕ) → (T.kronPow m).V i ⊗[K] (T.kronPow n).V i ≃ₗ[K]
      (T.kronPow (n + m)).V i
  | 0 => TensorProduct.lid K _
  | m + 1 => (TensorProduct.assoc K _ _ _).trans
      (TensorProduct.congr (LinearEquiv.refl K _) (appendMode T n i m))

private theorem interchange_tprod {K : Type u} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) = tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem interchange_assoc {K : Type u} [Field K]
    {V W U : Fin 3 → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W) (c : PiTensorProduct K U) :
    PiTensorProduct.map (fun i => (TensorProduct.assoc K (V i) (W i) (U i)).toLinearMap)
      (interchange (interchange a b) c) = interchange a (interchange b c) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod ca v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod cb w =>
      induction c using PiTensorProduct.induction_on with
      | smul_tprod cc x =>
        simp only [map_smul, LinearMap.smul_apply, smul_smul]
        rw [interchange_tprod, interchange_tprod, PiTensorProduct.map_tprod,
            interchange_tprod, interchange_tprod,
            show cc * (cb * ca) = cc * cb * ca from by ring]
        congr 1
      | add x y ih1 ih2 => simp only [map_add, ih1, ih2]
    | add x y ih1 ih2 => simp only [map_add, LinearMap.add_apply, ih1, ih2]
  | add x y ih1 ih2 => simp only [LinearMap.add_apply, map_add, ih1, ih2]

private theorem appendMode_tensor {K : Type u} [Field K]
    (T : TensorObj K 3) (n m : ℕ) :
    PiTensorProduct.map (fun i => (appendMode T n i m).toLinearMap)
      (interchange (T.kronPow m).t (T.kronPow n).t) = (T.kronPow (n + m)).t := by
  induction m with
  | zero =>
    change PiTensorProduct.map (fun i => (TensorProduct.lid K _).toLinearMap)
      (interchange (tprod K (fun _ : Fin 3 => (1 : K))) (T.kronPow n).t) = _
    induction (T.kronPow n).t using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      simp only [map_smul]
      rw [interchange_tprod, PiTensorProduct.map_tprod]
      simp only [LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul]
    | add x y ih1 ih2 => simp only [map_add, ih1, ih2]
  | succ m ih =>
    change PiTensorProduct.map (fun i =>
      (TensorProduct.map LinearMap.id (appendMode T n i m).toLinearMap) ∘ₗ
        (TensorProduct.assoc K _ _ _).toLinearMap)
      (interchange (interchange T.t (T.kronPow m).t) (T.kronPow n).t) = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, interchange_assoc,
      TensorObj.TypeGrading.kronMap_interchange, ih]
    simp only [PiTensorProduct.map_id, LinearMap.id_apply]
    rfl

private theorem appendMode_basis {K : Type u} [Field K]
    (T : TensorObj K 3) (i : Fin 3) {ι : Type u} (b : Basis ι K (T.V i))
    (n m : ℕ) (w : PowIndex ι m) (v : PowIndex ι n) :
    appendMode T n i m
      (kronPowModeBasis T i b m w ⊗ₜ[K] kronPowModeBasis T i b n v) =
      kronPowModeBasis T i b (n + m) (appendWord n m w v) := by
  induction m with
  | zero =>
    change TensorProduct.lid K _
      ((Basis.singleton (PowIndex ι 0) K) w ⊗ₜ[K] kronPowModeBasis T i b n v) = _
    rw [Basis.singleton_apply]
    rw [TensorProduct.lid_tmul, one_smul]
    rfl
  | succ m ih =>
    rcases w with ⟨a, w⟩
    change TensorProduct.congr (LinearEquiv.refl K _) (appendMode T n i m)
      (TensorProduct.assoc K _ _ _
        ((b.tensorProduct (kronPowModeBasis T i b m)) (a, w) ⊗ₜ[K]
          kronPowModeBasis T i b n v)) =
      (b.tensorProduct (kronPowModeBasis T i b (n + m)))
        (a, appendWord n m w v)
    rw [Basis.tensorProduct_apply, TensorProduct.assoc_tmul,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, ih, Basis.tensorProduct_apply]

/-- Concatenating two powers preserves their tensors and concatenates each mode's
numeric word basis in the same order. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) (n m : ℕ) :
    ∃ F : ∀ i, (T.kronPow m).V i ⊗[K] (T.kronPow n).V i ≃ₗ[K]
        (T.kronPow (n + m)).V i,
      PiTensorProduct.map (fun i => (F i).toLinearMap)
        (interchange (T.kronPow m).t (T.kronPow n).t) = (T.kronPow (n + m)).t ∧
      ∀ (i : Fin 3) (ι : Type u) (b : Basis ι K (T.V i)),
        ∃ join : (PowIndex ι m × PowIndex ι n) ≃ PowIndex ι (n + m),
          (∀ w v, F i (kronPowModeBasis T i b m w ⊗ₜ[K] kronPowModeBasis T i b n v) =
            kronPowModeBasis T i b (n + m) (join (w, v))) ∧
          (∀ w v (r : Fin m), PowIndex.get (n + m) (join (w, v)) ⟨r.val, by omega⟩ =
            PowIndex.get m w r) ∧
          (∀ w v (r : Fin n), PowIndex.get (n + m) (join (w, v)) ⟨m + r.val, by omega⟩ =
            PowIndex.get n v r) := by
  refine ⟨fun i => appendMode T n i m, appendMode_tensor T n m, ?_⟩
  intro i ι b
  refine ⟨appendWordEquiv ι n m, ?_, ?_, ?_⟩
  · simpa only [appendWordEquiv_apply] using appendMode_basis T i b n m
  · simpa only [appendWordEquiv_apply] using (appendWord_get_left (ι := ι) n m)
  · simpa only [appendWordEquiv_apply] using (appendWord_get_right (ι := ι) n m)

#print axioms solution
