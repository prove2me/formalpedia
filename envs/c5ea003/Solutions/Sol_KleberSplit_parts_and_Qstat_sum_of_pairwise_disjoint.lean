-- Prove2me | solution 1 for KleberSplit.parts_and_Qstat_sum_of_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:44:39.795254+00:00
-- url     : https://prove2.me/submissions/e015ff45-56f5-4fea-9673-59121b45be47

-- Sol generated from Algebra/KleberManyFoldProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Definitions.Def_Algebra_KleberManyFoldProducts
import Theorems.Thm_KleberSplit_Qstat_add
import Theorems.Thm_KleberSplit_dotp_eq_zero_iff
import Theorems.Thm_KleberSplit_parts_add_of_disjoint
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
    (u : κ → Exp N) (h : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (u j).support (u k).support) :
    parts (∑ j ∈ s, u j) = ∑ j ∈ s, parts (u j) ∧
      Qstat (∑ j ∈ s, u j) = ∑ j ∈ s, Qstat (u j) := by
  induction s using Finset.induction with
  | empty => simp [parts, Qstat]
  | insert j₀ t hj₀ ih =>
      have hsub : ∀ k ∈ t, k ∈ insert j₀ t := fun k hk => Finset.mem_insert_of_mem hk
      have hih := ih (fun a ha b hb hab => h a (hsub a ha) b (hsub b hb) hab)
      have hdisj : Disjoint (u j₀).support (∑ k ∈ t, u k).support := by
        refine Finset.disjoint_right.2 ?_
        intro i hi
        obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hi)
        have hne : j₀ ≠ k := fun hEq => hj₀ (hEq ▸ hk)
        exact Finset.disjoint_right.1
          (h j₀ (Finset.mem_insert_self _ _) k (hsub k hk) hne) hik
      rw [Finset.sum_insert hj₀, Finset.sum_insert hj₀, Finset.sum_insert hj₀,
        parts_add_of_disjoint hdisj, Qstat_add, (dotp_eq_zero_iff _ _).2 hdisj, hih.1, hih.2]
      exact ⟨rfl, by omega⟩
