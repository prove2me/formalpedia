-- Prove2me | solution 1 for Erdos390.rounding_error_zero_above_signature_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-16T14:02:29.095682+00:00
-- url     : https://prove2.me/submissions/55d5bddc-1bc1-4cb8-b5e9-d07de1514f83

import Definitions.Def_erdos390_prime_power_rounding
open scoped BigOperators
open Erdos390.WholePaper

/- Adapted from the pinned source cited in the explanation. -/
namespace Erdos390.WholePaper
noncomputable section

@[simp] private theorem mem_rowSet {A R : Type*} [Fintype A]
    {row : A → R} {r : R} {a : A} :
    a ∈ rowSet row r ↔ row a = r := by
  classical
  simp [rowSet]

theorem roundingValuationError_eq_zero_of_complete_rows
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (rowSignature : R → ℕ →₀ ℕ)
    (value : A → ℕ) (y : ℕ) (X x : A → ℝ)
    (hrows : ∀ r, ∑ a ∈ rowSet row r, X a =
      ∑ a ∈ rowSet row r, x a)
    (hsignature : ∀ a,
      completeRoughSignature y (value a) = rowSignature (row a))
    {q : ℕ} (hyq : y < q) :
    roundingValuationError value X x q = 0 := by
  classical
  unfold roundingValuationError
  rw [← Finset.sum_fiberwise Finset.univ row
    (fun a ↦ (X a - x a) * (value a).factorization q)]
  apply Finset.sum_eq_zero
  intro r _hr
  have hfactorization : ∀ a ∈ rowSet row r,
      (value a).factorization q = rowSignature r q := by
    intro a ha
    have haRow : row a = r := mem_rowSet.mp ha
    have happly := congrArg (fun s : ℕ →₀ ℕ ↦ s q) (hsignature a)
    change completeRoughSignature y (value a) q =
      rowSignature (row a) q at happly
    rw [completeRoughSignature_apply, if_pos hyq, haRow] at happly
    exact happly
  calc
    (∑ a ∈ Finset.univ with row a = r,
        (X a - x a) * (value a).factorization q) =
        ∑ a ∈ rowSet row r,
          (X a - x a) * (rowSignature r q : ℝ) := by
      apply Finset.sum_congr
      · rfl
      · intro a ha
        rw [hfactorization a ha]
    _ = (∑ a ∈ rowSet row r, (X a - x a)) *
        (rowSignature r q : ℝ) := by rw [Finset.sum_mul]
    _ = 0 := by
      rw [Finset.sum_sub_distrib, hrows r, sub_self, zero_mul]


end
end Erdos390.WholePaper

theorem solution
    {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (rowSignature : R → ℕ →₀ ℕ)
    (value : A → ℕ) (y : ℕ) (X x : A → ℝ)
    (hrows : ∀ r, ∑ a ∈ rowSet row r, X a =
      ∑ a ∈ rowSet row r, x a)
    (hsignature : ∀ a,
      completeRoughSignature y (value a) = rowSignature (row a))
    {q : ℕ} (hyq : y < q) :
    roundingValuationError value X x q = 0 := by
  exact roundingValuationError_eq_zero_of_complete_rows row rowSignature value y X x hrows hsignature hyq
