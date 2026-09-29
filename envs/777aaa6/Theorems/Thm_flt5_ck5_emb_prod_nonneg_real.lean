-- Prove2me | Theorems.Thm_flt5_ck5_emb_prod_nonneg_real
-- name    : flt5_ck5_emb_prod_nonneg_real
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T17:21:44.002043+00:00
-- url     : https://prove2.me/theorems/c31a8af1-1404-405e-bff7-28e0bf8aad18
-- statement:
--   The product of all complex embeddings σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ applied to x is a nonneg real number viewed as complex. Precisely: ∃ r : ℝ, 0 ≤ r ∧ (∏ σ, σ x) = ↑r. Proof: CK5 = ℚ(ζ₅) is totally imaginary, so its 4 complex embeddings pair under complex conjugation: (σ, conj∘σ) for two independent pairs. For each pair, σ(x) * conj(σ(x)) = Complex.normSq(σ x) ≥ 0 as a real number. The product over all 4 embeddings equals normSq(σ₁ x) * normSq(σ₂ x) for representatives σ₁, σ₂ from each pair, which is nonneg. This uses NumberField.ComplexEmbedding.conjugate for the pairing and Finset.prod_involution (or explicit enumeration) to split the product.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Norm.Transitivity

theorem flt5_ck5_emb_prod_nonneg_real (x : CyclotomicField 5 ℚ) : ∃ (r : ℝ), 0 ≤ r ∧ (∏ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, σ x) = ↑r := by sorry
