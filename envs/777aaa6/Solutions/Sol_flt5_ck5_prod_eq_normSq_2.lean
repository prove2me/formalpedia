-- Prove2me | solution 2 for flt5_ck5_prod_eq_normSq
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:57:10.236957+00:00
-- url     : https://prove2.me/submissions/1bb5af3e-3fd0-41d0-9173-ec4b27df3007
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Norm.Transitivity
import Theorems.Thm_flt5_ck5_prod_normSq_pair_exists

-- Proof: ∃ σ₁ σ₂, ∀ x : CK5, ∏ σ, σ x = ↑(normSq(σ₁ x) * normSq(σ₂ x)).
-- Strategy:
-- 1. Child flt5_ck5_prod_normSq_pair_exists gives σ₁, σ₂ independent of x such that
--    for ALL x, ∏ σ, σ x = ↑(normSq(σ₁ x) * normSq(σ₂ x)).
--    This uses: CK5 totally imaginary → 4 embeddings split into 2 conjugate pairs
--    {σ₁, conj σ₁} and {σ₂, conj σ₂}; each pair contributes normSq.
-- 2. Instantiate the child at the given x.

noncomputable section

abbrev CK5eqs := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5eqs :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5eqs :=
  IsCyclotomicExtension.numberField {5} ℚ CK5eqs

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

instance : IsGalois ℚ CK5eqs :=
  IsCyclotomicExtension.isGalois {5} ℚ CK5eqs

theorem solution (x : CK5eqs) :
    ∃ (σ₁ σ₂ : CK5eqs →ₐ[ℚ] ℂ),
    (∏ σ : CK5eqs →ₐ[ℚ] ℂ, σ x) = ↑(Complex.normSq (σ₁ x) * Complex.normSq (σ₂ x)) := by
  obtain ⟨σ₁, σ₂, h⟩ := flt5_ck5_prod_normSq_pair_exists
  exact ⟨σ₁, σ₂, h x⟩

end
