-- Prove2me | solution 1 for mme_CW_square_tensor_eq_sum_literal_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:13:27.403938+00:00
-- url     : https://prove2.me/submissions/a829c3c6-7754-484e-ae16-c15b91bb1785

import Theorems.Thm_mme_CWTensor_eq_sum_literal_terms
import Definitions.Def_mme_CW_fourth_literal_support_words

open MME TensorProduct Module BigOperators

universe u

set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem interchange_sum_right
    {K : Type u} [Field K] {d : ℕ} {ι : Type*} [Fintype ι]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (f : ι → PiTensorProduct K W) :
    interchange x (∑ i, f i) = ∑ i, interchange x (f i) := by
  exact map_sum (interchange x) f Finset.univ

private theorem interchange_sum_left
    {K : Type u} [Field K] {d : ℕ} {ι : Type*} [Fintype ι]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ι → PiTensorProduct K V) (y : PiTensorProduct K W) :
    interchange (∑ i, f i) y = ∑ i, interchange (f i) y := by
  have h :
      (interchange (∑ i, f i) :
        PiTensorProduct K W →ₗ[K]
          PiTensorProduct K (fun i => V i ⊗[K] W i)) =
        ∑ i, interchange (f i) :=
    map_sum interchange f Finset.univ
  simpa only [LinearMap.coe_sum, Finset.sum_apply] using
    congrArg (fun g => g y) h

/-- The literal CW square is the double sum of paired literal terms. -/
theorem solution
    (K : Type u) [Field K] (q : ℕ) :
    interchange (CWTensor K q) (CWTensor K q) =
      ∑ t₂ : MME.StothersFourth.CWLiteralTerm q,
      ∑ t₁ : MME.StothersFourth.CWLiteralTerm q,
        interchange
          (MME.StothersFourth.cwLiteralTermMonomial K q t₁)
          (MME.StothersFourth.cwLiteralTermMonomial K q t₂) := by
  rw [mme_CWTensor_eq_sum_literal_terms K q]
  simp only [interchange_sum_left, interchange_sum_right]
