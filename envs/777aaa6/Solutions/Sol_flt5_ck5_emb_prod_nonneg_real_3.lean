-- Prove2me | solution 3 for flt5_ck5_emb_prod_nonneg_real
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:56:03.742669+00:00
-- url     : https://prove2.me/submissions/f546f407-e867-46cb-945d-2abba3cb991d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Norm.Transitivity
import Theorems.Thm_flt5_ck5_prod_eq_normSq

-- Proof that ∃ r:ℝ, 0 ≤ r ∧ (∏ σ : CK5 →ₐ[ℚ] ℂ, σ x) = ↑r.
-- Strategy:
-- 1. Child flt5_ck5_prod_eq_normSq: gives σ₁, σ₂ such that the product of all 4
--    embeddings equals ↑(normSq(σ₁ x) * normSq(σ₂ x)).
--    This uses the conjugate pairing: CK5 is totally imaginary, so {σ,conj∘σ}
--    partition the embeddings, and each pair contributes σ(x)·conj(σ(x)) = normSq(σ(x)).
-- 2. normSq values are nonneg, so their product is nonneg.
-- 3. Package as the existential ∃ r:ℝ, 0 ≤ r ∧ product = ↑r.

noncomputable section

abbrev CK5npr := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5npr :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5npr :=
  IsCyclotomicExtension.numberField {5} ℚ CK5npr

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (x : CK5npr) :
    ∃ (r : ℝ), 0 ≤ r ∧ (∏ σ : CK5npr →ₐ[ℚ] ℂ, σ x) = ↑r := by
  -- Step 1: child gives σ₁, σ₂ with product = ↑(normSq(σ₁ x) * normSq(σ₂ x))
  obtain ⟨σ₁, σ₂, heq⟩ := flt5_ck5_prod_eq_normSq x
  -- Step 2: normSq ≥ 0, product ≥ 0, package the existential
  exact ⟨Complex.normSq (σ₁ x) * Complex.normSq (σ₂ x),
         mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _),
         heq⟩

end
