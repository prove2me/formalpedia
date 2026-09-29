-- Prove2me | solution 1 for KleberSplit.pairwise_disjoint_of_Qstat_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:44:39.294306+00:00
-- url     : https://prove2.me/submissions/f49b85f9-e4b5-4a05-a226-cd43709cb234

-- Sol generated from Algebra/KleberManyFoldProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Definitions.Def_Algebra_KleberManyFoldProducts
import Theorems.Thm_KleberSplit_Qstat_add
import Theorems.Thm_KleberSplit_dotp_eq_zero_iff
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


lemma support_subset_support_sum {κ : Type*} (s : Finset κ) (u : κ → Exp N) {j : κ}
    (hj : j ∈ s) : (u j).support ⊆ (∑ k ∈ s, u k).support := by
  intro i hi
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  have h1 : 0 < u j i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hi)
  have h2 : (u j) i ≤ ∑ k ∈ s, (u k) i :=
    Finset.single_le_sum (f := fun k => (u k) i) (fun k _ => Nat.zero_le _) hj
  omega

/-- Superadditivity of the quadratic statistic over finite sums. -/
lemma Qstat_sum_le {κ : Type*} [DecidableEq κ] (s : Finset κ) (u : κ → Exp N) :
    ∑ j ∈ s, Qstat (u j) ≤ Qstat (∑ j ∈ s, u j) := by
  induction s using Finset.induction with
  | empty => simp [Qstat]
  | insert j t hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Qstat_add]
      omega




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
    (u : κ → Exp N) (h : Qstat (∑ j ∈ s, u j) = ∑ j ∈ s, Qstat (u j)) :
    ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (u j).support (u k).support := by
  induction s using Finset.induction with
  | empty => simp
  | insert j₀ t hj₀ ih =>
      rw [Finset.sum_insert hj₀, Finset.sum_insert hj₀, Qstat_add] at h
      have hle := Qstat_sum_le t u
      have hdot : dotp (u j₀) (∑ k ∈ t, u k) = 0 := by omega
      have heq : Qstat (∑ k ∈ t, u k) = ∑ k ∈ t, Qstat (u k) := by omega
      have hdisj0 : Disjoint (u j₀).support (∑ k ∈ t, u k).support :=
        (dotp_eq_zero_iff _ _).1 hdot
      have hstep : ∀ k ∈ t, Disjoint (u j₀).support (u k).support := fun k hk =>
        hdisj0.mono_right (support_subset_support_sum t u hk)
      intro a ha b hb hab
      rcases Finset.mem_insert.1 ha with rfl | ha'
      · rcases Finset.mem_insert.1 hb with rfl | hb'
        · exact absurd rfl hab
        · exact hstep b hb'
      · rcases Finset.mem_insert.1 hb with rfl | hb'
        · exact (hstep a ha').symm
        · exact ih heq a ha' b hb' hab
