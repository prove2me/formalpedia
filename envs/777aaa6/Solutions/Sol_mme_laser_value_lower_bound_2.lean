-- Prove2me | solution 2 for mme_laser_value_lower_bound
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:26:55.920188+00:00
-- url     : https://prove2.me/submissions/e8fba3b4-20ba-4459-aa45-26040deebfd6

import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_subrank_capacity
open MME
universe u

open PiTensorProduct Filter

namespace MMELaserDisproof

variable {K : Type u} [Field K]

/-! ### Tensor-level facts: the zero family kills tensors, and direct summands of a
zero direct sum are zero. -/

/-- `PiTensorProduct.map` of the zero family sends every tensor to `0` (three modes). -/
lemma map_zero_family {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (y : PiTensorProduct K V) :
    PiTensorProduct.map (fun i => (0 : V i →ₗ[K] W i)) y = 0 := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [LinearMap.map_smul, PiTensorProduct.map_tprod]
    have h0 : (fun i => (0 : V i →ₗ[K] W i) (f i)) = (0 : ∀ i, W i) := by
      funext i; simp
    rw [h0, MultilinearMap.map_zero, smul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- If a direct sum `X ⊕ Y` has zero tensor, so does `X`. -/
lemma add_t_left {X Y : TensorObj K 3} (h : (TensorObj.add X Y).t = 0) : X.t = 0 := by
  have h1 : PiTensorProduct.map (fun i => LinearMap.fst K (X.V i) (Y.V i))
      (TensorObj.add X Y).t = 0 := by
    rw [h]; exact LinearMap.map_zero _
  have e : (TensorObj.add X Y).t =
      PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
      PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t := rfl
  rw [e, map_add] at h1
  have e1 : PiTensorProduct.map (fun i => LinearMap.fst K (X.V i) (Y.V i))
      (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t) = X.t := by
    have hc := LinearMap.congr_fun (PiTensorProduct.map_comp
      (fun i => LinearMap.fst K (X.V i) (Y.V i)) (fun i => LinearMap.inl K (X.V i) (Y.V i))) X.t
    rw [LinearMap.comp_apply] at hc
    rw [← hc]
    have hid : (fun i => LinearMap.fst K (X.V i) (Y.V i) ∘ₗ LinearMap.inl K (X.V i) (Y.V i)) =
        fun i => (LinearMap.id : X.V i →ₗ[K] X.V i) := by
      funext i; simp
    rw [hid, PiTensorProduct.map_id, LinearMap.id_apply]
  have e2 : PiTensorProduct.map (fun i => LinearMap.fst K (X.V i) (Y.V i))
      (PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t) = 0 := by
    have hc := LinearMap.congr_fun (PiTensorProduct.map_comp
      (fun i => LinearMap.fst K (X.V i) (Y.V i)) (fun i => LinearMap.inr K (X.V i) (Y.V i))) Y.t
    rw [LinearMap.comp_apply] at hc
    rw [← hc]
    have h0 : (fun i => LinearMap.fst K (X.V i) (Y.V i) ∘ₗ LinearMap.inr K (X.V i) (Y.V i)) =
        fun i => (0 : Y.V i →ₗ[K] X.V i) := by
      funext i; simp
    rw [h0]; exact map_zero_family Y.t
  rw [e1, e2, add_zero] at h1
  exact h1

/-- If a direct sum `X ⊕ Y` has zero tensor, so does `Y`. -/
lemma add_t_right {X Y : TensorObj K 3} (h : (TensorObj.add X Y).t = 0) : Y.t = 0 := by
  have h1 : PiTensorProduct.map (fun i => LinearMap.snd K (X.V i) (Y.V i))
      (TensorObj.add X Y).t = 0 := by
    rw [h]; exact LinearMap.map_zero _
  have e : (TensorObj.add X Y).t =
      PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
      PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t := rfl
  rw [e, map_add] at h1
  have e1 : PiTensorProduct.map (fun i => LinearMap.snd K (X.V i) (Y.V i))
      (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t) = 0 := by
    have hc := LinearMap.congr_fun (PiTensorProduct.map_comp
      (fun i => LinearMap.snd K (X.V i) (Y.V i)) (fun i => LinearMap.inl K (X.V i) (Y.V i))) X.t
    rw [LinearMap.comp_apply] at hc
    rw [← hc]
    have h0 : (fun i => LinearMap.snd K (X.V i) (Y.V i) ∘ₗ LinearMap.inl K (X.V i) (Y.V i)) =
        fun i => (0 : X.V i →ₗ[K] Y.V i) := by
      funext i; simp
    rw [h0]; exact map_zero_family X.t
  have e2 : PiTensorProduct.map (fun i => LinearMap.snd K (X.V i) (Y.V i))
      (PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t) = Y.t := by
    have hc := LinearMap.congr_fun (PiTensorProduct.map_comp
      (fun i => LinearMap.snd K (X.V i) (Y.V i)) (fun i => LinearMap.inr K (X.V i) (Y.V i))) Y.t
    rw [LinearMap.comp_apply] at hc
    rw [← hc]
    have hid : (fun i => LinearMap.snd K (X.V i) (Y.V i) ∘ₗ LinearMap.inr K (X.V i) (Y.V i)) =
        fun i => (LinearMap.id : Y.V i →ₗ[K] Y.V i) := by
      funext i; simp
    rw [hid, PiTensorProduct.map_id, LinearMap.id_apply]
  rw [e1, e2, zero_add] at h1
  exact h1

/-- If a finite direct sum has zero tensor, every summand has zero tensor. -/
lemma bigAdd_t_zero : ∀ {k : ℕ} (B : Fin k → TensorObj K 3),
    (TensorObj.bigAdd B).t = 0 → ∀ i, (B i).t = 0
  | 0, _, _, i => i.elim0
  | 1, B, h, i => by
      rw [Fin.fin_one_eq_zero i]; exact h
  | k + 2, B, h, i => by
      have h0 : (TensorObj.add (B 0) (TensorObj.bigAdd fun j => B j.succ)).t = 0 := h
      have hl := add_t_left h0
      have hr := add_t_right h0
      have ih := bigAdd_t_zero (fun j => B j.succ) hr
      exact Fin.cases hl (fun j => ih j) i

/-! ### The matrix-multiplication tensor is nonzero when all three dimensions are positive. -/

/-- The mode-wise data of the `(i, j, k)` term of `MMTensor K a b c`. -/
noncomputable def modeData (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    ∀ s : Fin 3, MMSpace K a b c s := fun s =>
  match s with
  | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin a × Fin b → K)
  | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin b × Fin c → K)
  | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin c × Fin a → K)

lemma MMTensor_eq_sum (a b c : ℕ) :
    MMTensor K a b c = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
      tprod K (modeData (K := K) a b c i j k) := rfl

/-- Evaluation of each mode at its `(0, 0)` coordinate. -/
noncomputable def ev0 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ s : Fin 3, MMSpace K a b c s →ₗ[K] K := fun s =>
  match s with
  | ⟨0, _⟩ => LinearMap.proj (R := K) (φ := fun _ : Fin a × Fin b => K) (⟨0, ha⟩, ⟨0, hb⟩)
  | ⟨1, _⟩ => LinearMap.proj (R := K) (φ := fun _ : Fin b × Fin c => K) (⟨0, hb⟩, ⟨0, hc⟩)
  | ⟨2, _⟩ => LinearMap.proj (R := K) (φ := fun _ : Fin c × Fin a => K) (⟨0, hc⟩, ⟨0, ha⟩)

/-- The linear functional `⨂ MMSpace → K` multiplying the three `(0,0)` coordinates. -/
noncomputable def Φ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    PiTensorProduct K (MMSpace K a b c) →ₗ[K] K :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra K (Fin 3) K).compLinearMap (ev0 (K := K) a b c ha hb hc))

lemma Φ_term (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    Φ (K := K) a b c ha hb hc (tprod K (modeData (K := K) a b c i j k)) =
      (if ((⟨0, ha⟩, ⟨0, hb⟩) : Fin a × Fin b) = (i, j) then (1 : K) else 0) *
      (if ((⟨0, hb⟩, ⟨0, hc⟩) : Fin b × Fin c) = (j, k) then (1 : K) else 0) *
      (if ((⟨0, hc⟩, ⟨0, ha⟩) : Fin c × Fin a) = (k, i) then (1 : K) else 0) := by
  unfold Φ
  rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_three]
  have e0 : ev0 (K := K) a b c ha hb hc 0 (modeData (K := K) a b c i j k 0) =
      (Pi.single (i, j) (1 : K) : Fin a × Fin b → K) (⟨0, ha⟩, ⟨0, hb⟩) := rfl
  have e1 : ev0 (K := K) a b c ha hb hc 1 (modeData (K := K) a b c i j k 1) =
      (Pi.single (j, k) (1 : K) : Fin b × Fin c → K) (⟨0, hb⟩, ⟨0, hc⟩) := rfl
  have e2 : ev0 (K := K) a b c ha hb hc 2 (modeData (K := K) a b c i j k 2) =
      (Pi.single (k, i) (1 : K) : Fin c × Fin a → K) (⟨0, hc⟩, ⟨0, ha⟩) := rfl
  rw [e0, e1, e2, Pi.single_apply, Pi.single_apply, Pi.single_apply]

lemma Φ_MMTensor (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Φ (K := K) a b c ha hb hc (MMTensor K a b c) = 1 := by
  rw [MMTensor_eq_sum]
  simp only [map_sum, Φ_term]
  rw [Fintype.sum_eq_single (⟨0, ha⟩ : Fin a)]
  · rw [Fintype.sum_eq_single (⟨0, hb⟩ : Fin b)]
    · rw [Fintype.sum_eq_single (⟨0, hc⟩ : Fin c)]
      · simp
      · intro k hk
        rw [if_neg (show ¬ (((⟨0, hb⟩, ⟨0, hc⟩) : Fin b × Fin c) = (⟨0, hb⟩, k)) from
          fun h => hk (Prod.mk.inj h).2.symm)]
        simp
    · intro j hj
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (show ¬ (((⟨0, ha⟩, ⟨0, hb⟩) : Fin a × Fin b) = (⟨0, ha⟩, j)) from
        fun h => hj (Prod.mk.inj h).2.symm)]
      simp
  · intro i hi
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (show ¬ (((⟨0, hc⟩, ⟨0, ha⟩) : Fin c × Fin a) = (k, i)) from
      fun h => hi (Prod.mk.inj h).2.symm)]
    simp

/-- `MMTensor K a b c = 0` forces one of the dimensions to vanish. -/
lemma mul_eq_zero_of_MMTensor_eq_zero {a b c : ℕ} (h : MMTensor K a b c = 0) :
    a * b * c = 0 := by
  by_contra hne
  have ha : 0 < a := Nat.pos_of_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
  have hb : 0 < b := Nat.pos_of_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul hne))
  have hc : 0 < c := Nat.pos_of_ne_zero (right_ne_zero_of_mul hne)
  have h1 := Φ_MMTensor (K := K) a b c ha hb hc
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-! ### The zero tensor object has subrank capacity `0`. -/

lemma zeroObj_t : (TensorObj.zeroObj : TensorObj K 3).t = 0 := rfl

lemma kronPow_zeroObj_t (N : ℕ) :
    (TensorObj.kronPow (TensorObj.zeroObj : TensorObj K 3) (N + 1)).t = 0 := by
  have e : (TensorObj.kronPow (TensorObj.zeroObj : TensorObj K 3) (N + 1)).t =
      interchange (TensorObj.zeroObj : TensorObj K 3).t
        (TensorObj.kronPow (TensorObj.zeroObj : TensorObj K 3) N).t := rfl
  rw [e, zeroObj_t, map_zero, LinearMap.zero_apply]
  rfl

lemma restrict_t_zero {X Y : TensorObj K 3} (hY : Y.t = 0) (h : TensorObj.Restrict X Y) :
    X.t = 0 := by
  obtain ⟨f, hf⟩ := h
  rw [hY, map_zero] at hf
  exact hf.symm

lemma subrankCapacity_zeroObj : subrankCapacity (TensorObj.zeroObj : TensorObj K 3) = 0 := by
  have hempty : ∀ V : ℝ, V ∉ {V : ℝ | 1 ≤ V ∧
      ∀ ε > (0 : ℝ), ∃ᶠ N in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((TensorObj.zeroObj : TensorObj K 3).kronPow N)
          ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ ((1 : ℝ) / 3)} := by
    intro V hV
    rcases hV with ⟨hV1, hV⟩
    have hfreq := hV (1 / 2) (by norm_num)
    obtain ⟨N, hN1, k, a, b, c, hres, hsum⟩ :=
      ((Filter.eventually_ge_atTop 1).and_frequently hfreq).exists
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hzero : (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i))).t = 0 :=
      restrict_t_zero (kronPow_zeroObj_t N') hres
    have hterm : ∀ i, a i * b i * c i = 0 := fun i =>
      mul_eq_zero_of_MMTensor_eq_zero (bigAdd_t_zero _ hzero i)
    have hsum0 : ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hterm i, Nat.cast_zero, Real.zero_rpow (by norm_num)]
    rw [hsum0] at hsum
    have hpow : (1 : ℝ) ≤ V ^ (N' + 1) := one_le_pow₀ hV1
    linarith
  unfold subrankCapacity
  convert Real.sSup_empty using 2
  ext V
  constructor
  · intro hV
    exact absurd hV (hempty V)
  · intro hV
    exact absurd hV (by simp)

/-- The (empty) `0`-way type grading of the zero object. -/
noncomputable def zeroGrading : (TensorObj.zeroObj : TensorObj K 3).TypeGrading 0 where
  decomp := fun _ => Fin.elim0
  is_internal := fun _ =>
    ⟨fun x y _ => Subsingleton.elim x y, fun _ => ⟨0, @Subsingleton.elim PUnit inferInstance _ _⟩⟩

end MMELaserDisproof

open MMELaserDisproof in
/-- Disproof at universe level `0`: the statement fails already for `K = ℚ`. -/
theorem solution : ¬ (∀ {K : Type} [Field K] {T : TensorObj K 3} {t : ℕ} (G : T.TypeGrading t)
    (S : Finset (Fin t × Fin t × Fin t)) (_hSym : LaserSymmetric S)
    (_hsupport : TensorObj.LaserAlignedSupport G S),
    laserValueFormula G S ≤ subrankCapacity T) := by
  intro h
  have hsym : LaserSymmetric (∅ : Finset (Fin 0 × Fin 0 × Fin 0)) := fun x hx => by simp at hx
  have hsupp : TensorObj.LaserAlignedSupport (zeroGrading (K := ℚ))
      (∅ : Finset (Fin 0 × Fin 0 × Fin 0)) :=
    ⟨0, Fin.elim0, Fin.elim0, by simp [zeroObj_t], fun j => j.elim0⟩
  have hle := @h ℚ _ TensorObj.zeroObj 0 zeroGrading ∅ hsym hsupp
  rw [subrankCapacity_zeroObj] at hle
  have h1 : laserValueFormula (K := ℚ) zeroGrading
      (∅ : Finset (Fin 0 × Fin 0 × Fin 0)) = 1 := rfl
  rw [h1] at hle
  norm_num at hle
