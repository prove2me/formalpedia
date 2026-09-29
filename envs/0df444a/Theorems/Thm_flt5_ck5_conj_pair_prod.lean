-- Prove2me | Theorems.Thm_flt5_ck5_conj_pair_prod
-- name    : flt5_ck5_conj_pair_prod
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T19:01:36.159387+00:00
-- url     : https://prove2.me/theorems/0013cbeb-3fee-4f7f-9186-ffd08b9837f3
-- statement:
--   There exist embeddings σ₁, σ₂ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ such that for all x : CK5, the product of all 4 complex embeddings applied to x equals ↑(normSq(σ₁ x) * normSq(σ₂ x)). This is proved by: CK5 = ℚ(ζ₅) has degree 4 and is totally imaginary. The 4 complex embeddings are determined by where ζ₅ maps: to ζ₅, ζ₅², ζ₅³, ζ₅⁴. Complex conjugation maps ζ₅^k to ζ₅^(5-k), so the pairs are {σ₁ (k=1), σ̄₁ (k=4)} and {σ₂ (k=2), σ̄₂ (k=3)}. The product σ₁(x)*σ̄₁(x)*σ₂(x)*σ̄₂(x) = normSq(σ₁ x)*normSq(σ₂ x) cast to ℂ. Uses NumberField.ComplexEmbedding.conjugate for the conjugation and Complex.normSq_eq_conj_mul_self for each pair.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Norm.Transitivity

theorem flt5_ck5_conj_pair_prod : ∃ (σ₁ σ₂ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ), ∀ (x : CyclotomicField 5 ℚ), (∏ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, σ x) = ↑(Complex.normSq (σ₁ x) * Complex.normSq (σ₂ x)) := by sorry
