-- Prove2me | solution 1 for mme_HasTauValueAtLeast_zero_tensor_iff
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:51:18.662694+00:00
-- url     : https://prove2.me/submissions/4a9fd072-b79f-4079-9c80-080e9d2169c8

import Definitions.Def_mme_tau_value
import Definitions.Def_mme_flattening
import Theorems.Thm_mme_flatteningRank_MMObj_ab
import Mathlib.Tactic

open MME MME.TensorObj BigOperators
universe u
set_option autoImplicit false

private theorem flatteningRank_zero {K : Type u} [Field K]
    {T : TensorObj K 3} (hT : T.t = 0) (σ : Split (Fin 3)) :
    flatteningRank σ T = 0 := by
  unfold flatteningRank flatteningMap
  rw [hT, map_zero, map_zero]
  rw [LinearMap.range_zero]
  exact finrank_bot _ _

private theorem matrix_volume_zero {K : Type u} [Field K] (a b c : ℕ)
    (h : (MMObj K a b c).t = 0) : a * b * c = 0 := by
  by_cases hc : c = 0
  · simp [hc]
  have hab := mme_flatteningRank_MMObj_ab (K := K) a b c (by omega)
  rw [flatteningRank_zero h] at hab
  have : a * b = 0 := by omega
  rw [this, zero_mul]

private theorem map_zero_modes {K : Type u} [Field K]
    (T S : TensorObj K 3) : PiTensorProduct.map (fun i ↦ (0 : T.V i →ₗ[K] S.V i)) T.t = 0 := by
  induction T.t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      rw [map_smul, PiTensorProduct.map_tprod]
      have hz : PiTensorProduct.tprod K (fun i ↦ (0 : T.V i →ₗ[K] S.V i) (v i)) = 0 :=
        (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3) rfl
      rw [hz, smul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

private theorem add_zero_components {K : Type u} [Field K] (S T : TensorObj K 3)
    (h : (TensorObj.add S T).t = 0) : S.t = 0 ∧ T.t = 0 := by
  have hf := congrArg (PiTensorProduct.map (fun i ↦ LinearMap.fst K (S.V i) (T.V i))) h
  have hs := congrArg (PiTensorProduct.map (fun i ↦ LinearMap.snd K (S.V i) (T.V i))) h
  change PiTensorProduct.map _ (PiTensorProduct.map _ S.t + PiTensorProduct.map _ T.t) = _ at hf hs
  simp only [map_add, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp] at hf hs
  simp only [LinearMap.fst_comp_inl, LinearMap.fst_comp_inr,
    LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, PiTensorProduct.map_id,
    LinearMap.id_apply] at hf hs
  rw [map_zero_modes T S, add_zero] at hf
  rw [map_zero_modes S T, zero_add] at hs
  exact ⟨hf, hs⟩

private theorem bigAdd_zero_components {K : Type u} [Field K]
    {k : ℕ} (B : Fin k → TensorObj K 3) (h : (TensorObj.bigAdd B).t = 0) :
    ∀ i, (B i).t = 0 := by
  induction k using Nat.twoStepInduction with
  | zero => intro i; exact Fin.elim0 i
  | one => intro i; have hi : i = 0 := Subsingleton.elim _ _; subst i; exact h
  | more k _ ih =>
      have hh := add_zero_components (B 0) (TensorObj.bigAdd (fun i ↦ B i.succ)) h
      intro i
      refine Fin.cases hh.1 (fun j ↦ ?_) i
      exact ih (fun j ↦ B j.succ) hh.2 j

/-- A restriction from a zero tensor has zero weighted matrix volume at every
nonzero real exponent. -/
theorem mme_zero_tensor_extraction_weight {K : Type u} [Field K]
    (T : TensorObj K 3) (hT : T.t = 0) (tau : ℝ) (htau : tau ≠ 0)
    (k : ℕ) (a b c : Fin k → ℕ)
    (h : TensorObj.Restrict (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))) T) :
    ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) = 0 := by
  obtain ⟨f, hf⟩ := h
  rw [hT, map_zero] at hf
  have hz := bigAdd_zero_components _ hf.symm
  apply Finset.sum_eq_zero
  intro i _
  rw [matrix_volume_zero (a i) (b i) (c i) (hz i), Nat.cast_zero, Real.zero_rpow htau]

private theorem kronPow_zero_tensor {K : Type u} [Field K]
    (T : TensorObj K 3) (hT : T.t = 0) {N : ℕ} (hN : 0 < N) :
    (T.kronPow N).t = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  change interchange T.t (T.kronPow n).t = 0
  rw [hT, map_zero, LinearMap.zero_apply]

/-- A zero tensor has only value zero at every nonzero real exponent. -/
theorem solution {K : Type u} [Field K]
    (T : TensorObj K 3) (hT : T.t = 0) (tau : ℝ) (htau : tau ≠ 0) (V : ℝ) :
    HasTauValueAtLeast T tau V ↔ V = 0 := by
  constructor
  · intro h
    by_contra hV
    have hpos : 0 < V := lt_of_le_of_ne h.1 (Ne.symm hV)
    have hf := h.2 (1 / 2) (by norm_num)
    obtain ⟨N, ⟨k, a, b, c, hr, hw⟩, hN⟩ :=
      (hf.and_eventually (Filter.eventually_gt_atTop 0)).exists
    have hz := mme_zero_tensor_extraction_weight (T.kronPow N)
      (kronPow_zero_tensor T hT hN) tau htau k a b c hr
    rw [hz] at hw
    have : 0 < V ^ N * (1 - (1 / 2 : ℝ)) := by positivity
    linarith
  · rintro rfl
    refine ⟨le_rfl, ?_⟩
    intro epsilon hepsilon
    apply Filter.Eventually.frequently
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_⟩
    · refine ⟨fun _ ↦ 0, ?_⟩
      change PiTensorProduct.map _ (T.kronPow N).t = 0
      rw [kronPow_zero_tensor T hT hN, map_zero]
      rfl
    · simp [zero_pow (Nat.ne_of_gt hN)]

