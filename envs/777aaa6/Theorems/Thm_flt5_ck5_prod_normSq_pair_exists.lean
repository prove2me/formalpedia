-- Prove2me | Theorems.Thm_flt5_ck5_prod_normSq_pair_exists
-- name    : flt5_ck5_prod_normSq_pair_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T17:47:21.484719+00:00
-- url     : https://prove2.me/theorems/f017a24a-9e42-462a-903d-04d886a9ae63
-- statement:
--   There exist two complex embeddings σ₁, σ₂ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ (independent of x) such that for any x : CK5, the product over all 4 complex embeddings equals ↑(Complex.normSq(σ₁ x) * Complex.normSq(σ₂ x)). Proof: CK5 is totally imaginary (degree 4, no real places), so its 4 complex embeddings split into exactly 2 conjugate pairs: {σ₁, NumberField.ComplexEmbedding.conjugate σ₁} and {σ₂, NumberField.ComplexEmbedding.conjugate σ₂}. Each pair contributes σᵢ(x) * (conj σᵢ)(x) = σᵢ(x) * starRingEnd ℂ (σᵢ(x)) = ↑(Complex.normSq(σᵢ x)) (by Complex.normSq_eq_conj_mul_self). The total product over all 4 embeddings = normSq(σ₁ x) * normSq(σ₂ x). Technically: use IsGalois ℚ CK5, the bijection between embeddings and (ZMod 5)ˣ via autEquivPow/autToPow, enumerate (ZMod 5)ˣ = {1,2,3,4}, and identify the conjugate pairs as {1,4} and {2,3} in (ZMod 5)ˣ (since conj maps ζ₅^k to ζ₅^{5-k}).

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Norm.Transitivity

theorem flt5_ck5_prod_normSq_pair_exists : ∃ (σ₁ σ₂ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ), ∀ (x : CyclotomicField 5 ℚ), (∏ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, σ x) = ↑(Complex.normSq (σ₁ x) * Complex.normSq (σ₂ x)) := by sorry
