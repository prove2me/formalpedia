-- Prove2me | solution 1 for ProofsInTheBook.Chapter32.chapter32
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:13:08.299707+00:00
-- url     : https://prove2.me/submissions/30aa6149-46a8-4126-998b-d4ac4af7568a

import Mathlib


/-!
# Chapter 32: Identities versus bijections

From "Proofs from THE BOOK":

The book compares analytic proofs (generating functions, algebraic
manipulations) with bijective proofs for combinatorial identities.

Formalized identities in this file:
- **Vandermonde's identity**: C(m+n, k) = ∑ᵢ C(m,i)·C(n,k-i)
- **Hockey-stick identity** (Zhu Shijie): ∑ᵢ₌ₖⁿ C(i,k) = C(n+1, k+1)
- **Binomial-coefficient sum**: ∑ₖ C(n,k) = 2ⁿ

Each identity admits both an algebraic proof and a bijective proof. The public
`chapter32` theorem below bundles these identities, rather than treating
Vandermonde as the sole endpoint of the chapter.
-/

namespace ProofsInTheBook.Chapter32

open Nat Finset Polynomial

/-!
### Vandermonde's identity

C(m+n, k) = ∑ᵢ C(m,i)·C(n,k-i). The bijective proof:
a k-element subset of an (m+n)-set splits by which
i elements come from the first m, and which k-i come from the last n.
-/

theorem chapter32_vandermonde (m n k : ℕ) :
    (m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2 :=
  calc
    (m + n).choose k = ((X + 1) ^ (m + n)).coeff k := by
      rw [coeff_X_add_one_pow, cast_id]
    _ = ((X + 1) ^ m * (X + 1) ^ n).coeff k := by
      rw [pow_add]
    _ = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
      rw [coeff_mul, Finset.sum_congr rfl]
      simp only [coeff_X_add_one_pow, cast_id, imp_true_iff]

/-!
### Hockey-stick identity

∑ᵢ₌ₖⁿ C(i,k) = C(n+1, k+1). Bijective proof:
a (k+1)-subset of {0,...,n} is determined by its maximum element i,
with the remaining k elements forming a k-subset of {0,...,i-1} ≅ {1,...,i}.
-/

theorem chapter32_hockey_stick (n k : ℕ) :
    ∑ i ∈ Icc k n, i.choose k = (n + 1).choose (k + 1) :=
  by
    rcases lt_or_ge n k with h | h
    · rw [choose_eq_zero_of_lt (by omega), Icc_eq_empty_of_lt h, sum_empty]
    · induction n, h using le_induction with
      | base => simp
      | succ n _ ih =>
        rw [← Ico_insert_right (by omega), sum_insert (by simp),
          Ico_add_one_right_eq_Icc, ih, choose_succ_succ' (n + 1)]

/-!
### Binomial theorem: sum of all binomial coefficients

∑ₖ₌₀ⁿ C(n,k) = 2ⁿ.
-/

theorem chapter32_binomial_sum (n : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k = 2 ^ n :=
  by
    have h := (add_pow 1 1 n).symm
    simpa [one_add_one_eq_two] using h



end ProofsInTheBook.Chapter32

open Nat Finset Polynomial
open ProofsInTheBook.Chapter32

theorem solution :
    (∀ m n k : ℕ,
        (m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2) ∧
      (∀ n k : ℕ, ∑ i ∈ Icc k n, i.choose k = (n + 1).choose (k + 1)) ∧
      (∀ n : ℕ, ∑ k ∈ range (n + 1), n.choose k = 2 ^ n) :=
  ⟨chapter32_vandermonde, chapter32_hockey_stick, chapter32_binomial_sum⟩
