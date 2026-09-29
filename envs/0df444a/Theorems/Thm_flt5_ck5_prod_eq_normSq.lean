-- Prove2me | Theorems.Thm_flt5_ck5_prod_eq_normSq
-- name    : flt5_ck5_prod_eq_normSq
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T17:29:17.936407+00:00
-- url     : https://prove2.me/theorems/e9711578-b773-4c27-9024-90d437d88d85
-- statement:
--   For any x : CyclotomicField 5 ℚ, the product of all 4 complex embeddings σ : CK5 →ₐ[ℚ] ℂ equals ↑(Complex.normSq(σ₁ x) * Complex.normSq(σ₂ x)) for some two embeddings σ₁, σ₂. Proof: CK5 is totally imaginary, so the 4 embeddings split into 2 conjugate pairs {σ₁, conj∘σ₁} and {σ₂, conj∘σ₂}. Each pair contributes σᵢ(x) * (conj∘σᵢ)(x) = σᵢ(x) * starRingEnd ℂ (σᵢ(x)) = Complex.normSq(σᵢ x) (a nonneg real viewed as complex). The product over all 4 embeddings is therefore normSq(σ₁ x) * normSq(σ₂ x), cast to ℂ. Technically: use NumberField.ComplexEmbedding.conjugate for the pairing and Finset.prod_involution (or explicit enumeration of the 4 embeddings using autToPow) to split the product.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Norm.Transitivity

theorem flt5_ck5_prod_eq_normSq (x : CyclotomicField 5 ℚ) : ∃ (σ₁ σ₂ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ), (∏ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, σ x) = ↑(Complex.normSq (σ₁ x) * Complex.normSq (σ₂ x)) := by sorry
