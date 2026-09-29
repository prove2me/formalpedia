-- Prove2me | solution 1 for KleberSplit.exists_pairwise_disjoint_placement
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:21:24.151144+00:00
-- url     : https://prove2.me/submissions/4d64179d-cfd8-402a-b62d-54b32163adc3

-- Sol generated from Algebra/KleberManyFoldProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Definitions.Def_Algebra_KleberManyFoldProducts
import Theorems.Thm_KleberSplit_equivMapDomain_mem_orbit
import Theorems.Thm_KleberSplit_exists_placement_avoiding
import Theorems.Thm_KleberSplit_support_equivMapDomain
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

lemma card_support_equivMapDomain (e : Equiv.Perm (Fin N)) (b : Exp N) :
    (Finsupp.equivMapDomain e b).support.card = b.support.card := by
  rw [support_equivMapDomain, Finset.card_map]






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
    (f : κ → Exp N) (F : Finset (Fin N)) (h : F.card + ∑ j ∈ s, (f j).support.card ≤ N) :
    ∃ u : κ → Exp N, (∀ j ∈ s, u j ∈ orbit (f j)) ∧ (∀ j ∈ s, Disjoint F (u j).support) ∧
      (∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (u j).support (u k).support) := by
  induction s using Finset.induction generalizing F with
  | empty => exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  | insert j₀ t hj₀ ih =>
      rw [Finset.sum_insert hj₀] at h
      obtain ⟨e₀, he₀⟩ := exists_placement_avoiding F (f j₀) (by omega)
      set u₀ : Exp N := Finsupp.equivMapDomain e₀ (f j₀) with hu₀
      have hcard₀ : u₀.support.card = (f j₀).support.card :=
        card_support_equivMapDomain e₀ (f j₀)
      have hunion : (F ∪ u₀.support).card = F.card + (f j₀).support.card := by
        rw [Finset.card_union_of_disjoint he₀, hcard₀]
      obtain ⟨u, hu_orbit, hu_avoid, hu_pair⟩ := ih (F := F ∪ u₀.support) (by omega)
      refine ⟨Function.update u j₀ u₀, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj'
        · simpa [hu₀] using equivMapDomain_mem_orbit e₀ (f j)
        · have hne : j ≠ j₀ := fun hEq => hj₀ (hEq ▸ hj')
          simpa [Function.update_of_ne hne] using hu_orbit j hj'
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj'
        · simpa using he₀
        · have hne : j ≠ j₀ := fun hEq => hj₀ (hEq ▸ hj')
          have := hu_avoid j hj'
          rw [Finset.disjoint_union_left] at this
          simpa [Function.update_of_ne hne] using this.1
      · intro j hj k hk hjk
        have key : ∀ m ∈ t, Disjoint u₀.support (u m).support := by
          intro m hm
          have := hu_avoid m hm
          rw [Finset.disjoint_union_left] at this
          exact this.2
        rcases Finset.mem_insert.1 hj with rfl | hj'
        · rcases Finset.mem_insert.1 hk with rfl | hk'
          · exact absurd rfl hjk
          · have hne : k ≠ j := fun hEq => hj₀ (hEq ▸ hk')
            simpa [Function.update_of_ne hne] using key k hk'
        · rcases Finset.mem_insert.1 hk with rfl | hk'
          · have hne : j ≠ k := fun hEq => hj₀ (hEq ▸ hj')
            simpa [Function.update_of_ne hne] using (key j hj').symm
          · have hnej : j ≠ j₀ := fun hEq => hj₀ (hEq ▸ hj')
            have hnek : k ≠ j₀ := fun hEq => hj₀ (hEq ▸ hk')
            simpa [Function.update_of_ne hnej, Function.update_of_ne hnek] using
              hu_pair j hj' k hk' hjk
