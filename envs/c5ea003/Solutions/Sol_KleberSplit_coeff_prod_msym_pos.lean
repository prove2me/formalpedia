-- Prove2me | solution 1 for KleberSplit.coeff_prod_msym_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:09:44.943272+00:00
-- url     : https://prove2.me/submissions/f5186fc0-5f5c-4b3b-9056-a3810c897175

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
theorem solution{κ : Type*} [DecidableEq κ] (s : Finset κ) (f u : κ → Exp N)
    (hu : ∀ j ∈ s, u j ∈ orbit (f j)) :
    0 < MvPolynomial.coeff (∑ j ∈ s, u j) (∏ j ∈ s, msym ℕ (f j)) := by
  induction s using Finset.induction with
  | empty => simp
  | insert j₀ t hj₀ ih =>
      have hsub : ∀ k ∈ t, k ∈ insert j₀ t := fun k hk => Finset.mem_insert_of_mem hk
      have hpos := ih (fun k hk => hu k (hsub k hk))
      rw [Finset.prod_insert hj₀, Finset.sum_insert hj₀, MvPolynomial.coeff_mul]
      have hmem : (u j₀, ∑ k ∈ t, u k) ∈ Finset.antidiagonal (u j₀ + ∑ k ∈ t, u k) := by
        simp
      have hterm : 0 < MvPolynomial.coeff (u j₀) (msym ℕ (f j₀)) *
          MvPolynomial.coeff (∑ k ∈ t, u k) (∏ j ∈ t, msym ℕ (f j)) := by
        rw [coeff_msym, if_pos (hu j₀ (Finset.mem_insert_self _ _))]
        simpa using hpos
      calc 0 < MvPolynomial.coeff (u j₀) (msym ℕ (f j₀)) *
            MvPolynomial.coeff (∑ k ∈ t, u k) (∏ j ∈ t, msym ℕ (f j)) := hterm
        _ ≤ _ := Finset.single_le_sum
            (f := fun x : Exp N × Exp N => MvPolynomial.coeff x.1 (msym ℕ (f j₀)) *
              MvPolynomial.coeff x.2 (∏ j ∈ t, msym ℕ (f j)))
            (fun x _ => Nat.zero_le _) hmem
