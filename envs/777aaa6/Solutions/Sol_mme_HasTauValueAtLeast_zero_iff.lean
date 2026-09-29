-- Prove2me | solution 1 for mme_HasTauValueAtLeast_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:46:34.977584+00:00
-- url     : https://prove2.me/submissions/4f9614da-a631-4770-96ac-4ae9c7337d03

import Definitions.Def_mme_tau_value
import Mathlib.Tactic

open MME BigOperators Filter
universe u
set_option autoImplicit false

/-!
At exponent zero, a zero-volume matrix block contributes one to the
unrestricted value sum. The definition permits arbitrarily many such blocks.
-/

private theorem zero_matrix_sum_tensor {K : Type u} [Field K] (k : ℕ) :
    (TensorObj.bigAdd (fun _ : Fin k ↦ MMObj K 0 0 0)).t = 0 := by
  have hmm : (MMObj K 0 0 0).t = 0 := by
    change MMTensor K 0 0 0 = 0
    simp [MMTensor]
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => exact hmm
  | more k _ ih =>
      change PiTensorProduct.map _ (MMObj K 0 0 0).t +
        PiTensorProduct.map _
          (TensorObj.bigAdd (fun _ : Fin (k + 1) ↦ MMObj K 0 0 0)).t = 0
      rw [hmm, ih, map_zero, map_zero]
      exact add_zero _

private theorem restrict_zero_matrix_sum {K : Type u} [Field K]
    (T : TensorObj K 3) (k : ℕ) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin k ↦ MMObj K 0 0 0)) T := by
  refine ⟨fun _ ↦ 0, ?_⟩
  rw [zero_matrix_sum_tensor]
  induction T.t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      rw [map_smul, PiTensorProduct.map_tprod]
      have hz : PiTensorProduct.tprod K (fun i ↦
          (0 : T.V i →ₗ[K]
            (TensorObj.bigAdd (fun _ : Fin k ↦ MMObj K 0 0 0)).V i) (v i)) = 0 :=
        (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3) rfl
      rw [hz, smul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- With the current unrestricted block convention, every tensor has every
nonnegative value at exponent zero. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) (V : ℝ) :
    HasTauValueAtLeast T 0 V ↔ 0 ≤ V := by
  refine ⟨fun h ↦ h.1, fun hV ↦ ⟨hV, ?_⟩⟩
  intro epsilon hepsilon
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro N
  let k : ℕ := ⌈V ^ N * (1 - epsilon)⌉₊
  refine ⟨k, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0,
    restrict_zero_matrix_sum (T.kronPow N) k, ?_⟩
  simpa using (Nat.le_ceil (V ^ N * (1 - epsilon)))

