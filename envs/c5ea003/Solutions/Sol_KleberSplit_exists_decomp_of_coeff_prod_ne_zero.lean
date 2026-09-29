-- Prove2me | solution 1 for KleberSplit.exists_decomp_of_coeff_prod_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:09:46.705019+00:00
-- url     : https://prove2.me/submissions/1d02451e-f386-422a-a00d-6ef479ea41af

-- Sol generated from Algebra/KleberManyFoldProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Definitions.Def_Algebra_KleberManyFoldProducts
import Theorems.Thm_KleberSplit_coeff_msym
/-
# Many-fold complementary products of monomial symmetric functions

A continuation of `Algebra.KleberComplementaryProducts`.  The quadratic-statistic
triangularity used there for products of *two* monomial symmetric functions is not tied to
two factors: here we prove that products `m_{α_1} ⋯ m_{α_r}` of arbitrarily many monomial
symmetric functions are linearly independent as soon as the multiset unions
`parts α_1 + ⋯ + parts α_r` are pairwise distinct.

## Main results

* `KleberSplit.linearIndependent_msym_prod` — many-fold independence.
* `KleberSplit.linearIndependent_psum_monomials` — corollary: linear independence of
  power-sum monomials `p_{k_1} ⋯ p_{k_r}` indexed by multisets of positive exponents.
-/


open KleberSplit

open Finsupp MvPolynomial Finset

variable {N : ℕ} {R : Type*} [CommRing R] {S : Type*} [CommSemiring S]

/-! ### Products of arbitrarily many factors

The mechanism above is not restricted to *two* factors.  We now prove the sharper
statement: products `m_{α_1} ⋯ m_{α_r}` of arbitrarily many monomial symmetric functions
are linearly independent as soon as the multiset unions `parts α_1 + ⋯ + parts α_r` are
pairwise distinct.  For `r = 2` this recovers the theorem above.
-/







/-! #### Coefficients of many-fold products -/






/-! ### Application: linear independence of power-sum monomials

Since `m_{(k)} = p_k` is the power sum, a product `∏_j p_{k_j}` is a monomial in the power
sums, and its multiset union is exactly the multiset `{k_j}` of exponents.  The many-fold
theorem therefore recovers the linear independence of the power-sum monomials
`p_{k_1} ⋯ p_{k_r}` indexed by multisets of positive integers, provided there are at least
as many variables as factors.
-/







open KleberSplit in
theorem solution{κ : Type*} [DecidableEq κ] (s : Finset κ)
    (f : κ → Exp N) (w : Exp N)
    (h : MvPolynomial.coeff w (∏ j ∈ s, msym ℕ (f j)) ≠ 0) :
    ∃ u : κ → Exp N, (∀ j ∈ s, u j ∈ orbit (f j)) ∧ ∑ j ∈ s, u j = w := by
  induction s using Finset.induction generalizing w with
  | empty =>
      refine ⟨fun _ => 0, by simp, ?_⟩
      simp only [Finset.prod_empty, MvPolynomial.coeff_one] at h
      simp only [Finset.sum_empty]
      by_contra hne
      simp [hne] at h
  | insert j₀ t hj₀ ih =>
      rw [Finset.prod_insert hj₀, MvPolynomial.coeff_mul] at h
      obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have hx1 : x.1 ∈ orbit (f j₀) := by
        by_contra hc
        rw [coeff_msym, if_neg hc] at hxne
        simp at hxne
      have hx2 : MvPolynomial.coeff x.2 (∏ j ∈ t, msym ℕ (f j)) ≠ 0 := by
        intro hc
        rw [hc] at hxne
        simp at hxne
      obtain ⟨u, hu, hsum⟩ := ih x.2 hx2
      refine ⟨Function.update u j₀ x.1, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj'
        · simpa using hx1
        · have hne : j ≠ j₀ := fun hEq => hj₀ (hEq ▸ hj')
          simpa [Function.update_of_ne hne] using hu j hj'
      · rw [Finset.sum_insert hj₀, Function.update_self]
        have : ∑ j ∈ t, Function.update u j₀ x.1 j = ∑ j ∈ t, u j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hne : j ≠ j₀ := fun hEq => hj₀ (hEq ▸ hj)
          simp [Function.update_of_ne hne]
        rw [this, hsum]
        simpa using (Finset.mem_antidiagonal.1 hx)
