-- Prove2me | solution 1 for KleberSplit.linearIndependent_psum_monomials
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:12:33.731893+00:00
-- url     : https://prove2.me/submissions/252a47ee-30d5-4836-8574-d3f727559853

-- Sol generated from Algebra/KleberManyFoldProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Definitions.Def_Algebra_KleberManyFoldProducts
import Theorems.Thm_KleberSplit_card_support_single_le
import Theorems.Thm_KleberSplit_linearIndependent_msym_prod
import Theorems.Thm_KleberSplit_parts_single
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

/-- The orbit of a one-row exponent vector consists of all one-row exponent vectors. -/
lemma orbit_single (i : Fin N) (x : ℕ) :
    orbit (Finsupp.single i x) = Finset.univ.image (fun j : Fin N => Finsupp.single j x) := by
  ext w
  simp only [orbit, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e i, by rw [Finsupp.equivMapDomain_single]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Equiv.swap i j, by rw [Finsupp.equivMapDomain_single, Equiv.swap_apply_left]⟩


/-- A one-row monomial symmetric polynomial is a power sum. -/
lemma msym_single_eq_psum (i : Fin N) {x : ℕ} (hx : x ≠ 0) :
    msym R (Finsupp.single i x) = KleberSplit.psum R N x := by
  unfold msym KleberSplit.psum
  rw [orbit_single, Finset.sum_image (fun a _ b _ hab => Finsupp.single_left_injective hx hab)]
  exact Finset.sum_congr rfl fun j _ => (MvPolynomial.X_pow_eq_monomial).symm

lemma multiset_map_eq_sum_singleton {κ : Type*} (s : Finset κ) (k : κ → ℕ) :
    (s.val.map k : Multiset ℕ) = ∑ j ∈ s, ({k j} : Multiset ℕ) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih =>
      rw [Finset.cons_val, Multiset.map_cons, Finset.sum_cons, ih, Multiset.singleton_add]



open KleberSplit in
theorem solution{M : ℕ} [IsDomain R] [CharZero R]
    {ι κ : Type*} [Fintype ι] [DecidableEq κ] (s : Finset κ) (k : ι → κ → ℕ)
    (hk : ∀ i, ∀ j ∈ s, k i j ≠ 0) (hcard : s.card ≤ M + 1)
    (hinj : Function.Injective fun i => (s.val.map (k i) : Multiset ℕ)) :
    LinearIndependent R (fun i => ∏ j ∈ s, KleberSplit.psum R (M + 1) (k i j)) := by
  set f : ι → κ → Exp (M + 1) := fun i j => Finsupp.single (0 : Fin (M + 1)) (k i j) with hf
  have hprod : ∀ i, ∏ j ∈ s, KleberSplit.psum R (M + 1) (k i j) = ∏ j ∈ s, msym R (f i j) :=
    fun i => Finset.prod_congr rfl fun j hj => (msym_single_eq_psum 0 (hk i j hj)).symm
  have hparts : ∀ i, ∑ j ∈ s, parts (f i j) = (s.val.map (k i) : Multiset ℕ) := by
    intro i
    rw [multiset_map_eq_sum_singleton]
    exact Finset.sum_congr rfl fun j hj => by
      rw [hf]; simp [parts_single, hk i j hj]
  have hcard' : ∀ i, ∑ j ∈ s, (f i j).support.card ≤ M + 1 := by
    intro i
    refine le_trans (Finset.sum_le_sum fun j _ => card_support_single_le _ _) ?_
    simpa using hcard
  have := linearIndependent_msym_prod (R := R) s f hcard'
    (by
      intro i₁ i₂ h
      simp only [hparts] at h
      exact hinj h)
  simpa only [hprod] using this
