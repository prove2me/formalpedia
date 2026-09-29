-- Prove2me | solution 3 for flt5_ck5_prod_emb_nonneg
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:52:35.380002+00:00
-- url     : https://prove2.me/submissions/810ed0b1-b0d6-4393-8a15-70017d60e9f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Norm.Transitivity
import Theorems.Thm_flt5_ck5_emb_prod_nonneg_real

-- Proof that 0 ≤ (∏ σ : CK5 →ₐ[ℚ] ℂ, σ x).re
-- Strategy:
-- 1. Child flt5_ck5_emb_prod_nonneg_real: the product of all complex embeddings
--    is a nonneg real (viewed as complex). This uses the conjugate pairing:
--    CK5 is totally imaginary so embeddings pair under conj, each pair gives normSq ≥ 0.
-- 2. The real part of a nonneg real cast to ℂ is that real, hence ≥ 0.

noncomputable section

abbrev CK5pe := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5pe :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5pe :=
  IsCyclotomicExtension.numberField {5} ℚ CK5pe

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (x : CK5pe) : 0 ≤ (∏ σ : CK5pe →ₐ[ℚ] ℂ, σ x).re := by
  -- Step 1: the product is a nonneg real r viewed as complex
  obtain ⟨r, hr, heq⟩ := flt5_ck5_emb_prod_nonneg_real x
  -- Step 2: (↑r : ℂ).re = r ≥ 0
  simp only [heq, Complex.ofReal_re]
  exact hr

end
