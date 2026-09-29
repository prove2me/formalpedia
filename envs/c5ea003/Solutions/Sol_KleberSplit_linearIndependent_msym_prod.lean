-- Prove2me | solution 1 for KleberSplit.linearIndependent_msym_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:58:33.631345+00:00
-- url     : https://prove2.me/submissions/20a5fe72-0775-4a71-9383-4a44b40c0eae

-- Sol generated from Algebra/KleberManyFoldProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Definitions.Def_Algebra_KleberManyFoldProducts
import Theorems.Thm_KleberSplit_Qstat_add
import Theorems.Thm_KleberSplit_Qstat_of_mem_orbit
import Theorems.Thm_KleberSplit_coeff_prod_msym_pos
import Theorems.Thm_KleberSplit_exists_decomp_of_coeff_prod_ne_zero
import Theorems.Thm_KleberSplit_exists_pairwise_disjoint_placement
import Theorems.Thm_KleberSplit_pairwise_disjoint_of_Qstat_sum_eq
import Theorems.Thm_KleberSplit_parts_and_Qstat_sum_of_pairwise_disjoint
import Theorems.Thm_KleberSplit_parts_of_mem_orbit
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



/-- Superadditivity of the quadratic statistic over finite sums. -/
lemma Qstat_sum_le {κ : Type*} [DecidableEq κ] (s : Finset κ) (u : κ → Exp N) :
    ∑ j ∈ s, Qstat (u j) ≤ Qstat (∑ j ∈ s, u j) := by
  induction s using Finset.induction with
  | empty => simp [Qstat]
  | insert j t hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Qstat_add]
      omega




/-! #### Coefficients of many-fold products -/

lemma msym_map (d : Exp N) :
    MvPolynomial.map (Nat.castRingHom S) (msym ℕ d) = msym S d := by
  unfold msym
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [MvPolynomial.map_monomial]

lemma coeff_prod_msym_cast {κ : Type*} (s : Finset κ) (f : κ → Exp N) (w : Exp N) :
    MvPolynomial.coeff w (∏ j ∈ s, msym S (f j))
      = ((MvPolynomial.coeff w (∏ j ∈ s, msym ℕ (f j)) : ℕ) : S) := by
  have : (∏ j ∈ s, msym S (f j))
      = MvPolynomial.map (Nat.castRingHom S) (∏ j ∈ s, msym ℕ (f j)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun j _ => (msym_map (f j)).symm
  rw [this, MvPolynomial.coeff_map]
  simp




/-! ### Application: linear independence of power-sum monomials

Since `m_{(k)} = p_k` is the power sum, a product `∏_j p_{k_j}` is a monomial in the power
sums, and its multiset union is exactly the multiset `{k_j}` of exponents.  The many-fold
theorem therefore recovers the linear independence of the power-sum monomials
`p_{k_1} ⋯ p_{k_r}` indexed by multisets of positive integers, provided there are at least
as many variables as factors.
-/







open KleberSplit in
theorem solution[IsDomain R] [CharZero R]
    {ι κ : Type*} [Fintype ι] [DecidableEq κ] (s : Finset κ) (f : ι → κ → Exp N)
    (hcard : ∀ i, ∑ j ∈ s, (f i j).support.card ≤ N)
    (hinj : Function.Injective fun i => ∑ j ∈ s, parts (f i j)) :
    LinearIndependent R (fun i => ∏ j ∈ s, msym R (f i j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  by_contra hcon
  push_neg at hcon
  obtain ⟨g, hg, i₁, hi₁⟩ := hcon
  set S : Finset ι := Finset.univ.filter (fun i => g i ≠ 0) with hS
  have hSne : S.Nonempty := ⟨i₁, by simp [hS, hi₁]⟩
  obtain ⟨i₀, hi₀S, hmin⟩ :=
    S.exists_min_image (fun i => ∑ j ∈ s, Qstat (f i j)) hSne
  have hg₀ : g i₀ ≠ 0 := by simpa [hS] using hi₀S
  obtain ⟨u, hu_orbit, -, hu_pair⟩ :=
    exists_pairwise_disjoint_placement s (f i₀) ∅ (by simpa using hcard i₀)
  set w₀ : Exp N := ∑ j ∈ s, u j with hw₀
  have hu_parts : ∀ j ∈ s, parts (u j) = parts (f i₀ j) := fun j hj =>
    parts_of_mem_orbit (hu_orbit j hj)
  have hu_Q : ∀ j ∈ s, Qstat (u j) = Qstat (f i₀ j) := fun j hj =>
    Qstat_of_mem_orbit (hu_orbit j hj)
  obtain ⟨hpartsw₀', hQw₀'⟩ := parts_and_Qstat_sum_of_pairwise_disjoint s u hu_pair
  have hQw₀ : Qstat w₀ = ∑ j ∈ s, Qstat (f i₀ j) := by
    rw [hw₀, hQw₀']
    exact Finset.sum_congr rfl hu_Q
  have hpartsw₀ : parts w₀ = ∑ j ∈ s, parts (f i₀ j) := by
    rw [hw₀, hpartsw₀']
    exact Finset.sum_congr rfl hu_parts
  -- take the coefficient of `w₀` in the vanishing relation
  have hcoeff := congrArg (MvPolynomial.coeff w₀) hg
  rw [MvPolynomial.coeff_sum] at hcoeff
  simp only [smul_eq_mul, MvPolynomial.coeff_smul, MvPolynomial.coeff_zero] at hcoeff
  have hvanish : ∀ i ∈ Finset.univ, i ≠ i₀ →
      g i * MvPolynomial.coeff w₀ (∏ j ∈ s, msym R (f i j)) = 0 := by
    intro i _ hne
    by_cases hgi : g i = 0
    · simp [hgi]
    have hiS : i ∈ S := by simp [hS, hgi]
    by_cases hc : MvPolynomial.coeff w₀ (∏ j ∈ s, msym R (f i j)) = 0
    · simp [hc]
    exfalso
    rw [coeff_prod_msym_cast] at hc
    have hcnat : MvPolynomial.coeff w₀ (∏ j ∈ s, msym ℕ (f i j)) ≠ 0 := by
      intro h0
      rw [h0] at hc
      simp at hc
    obtain ⟨v, hv_orbit, hv_sum⟩ := exists_decomp_of_coeff_prod_ne_zero s (f i) w₀ hcnat
    have hvQ : ∀ j ∈ s, Qstat (v j) = Qstat (f i j) := fun j hj =>
      Qstat_of_mem_orbit (hv_orbit j hj)
    have hle1 : ∑ j ∈ s, Qstat (f i j) ≤ Qstat w₀ := by
      rw [← hv_sum]
      refine le_trans (le_of_eq ?_) (Qstat_sum_le s v)
      exact (Finset.sum_congr rfl hvQ).symm
    have hle2 : ∑ j ∈ s, Qstat (f i₀ j) ≤ ∑ j ∈ s, Qstat (f i j) := hmin i hiS
    have hEq : Qstat (∑ j ∈ s, v j) = ∑ j ∈ s, Qstat (v j) := by
      rw [hv_sum, Finset.sum_congr rfl hvQ]
      omega
    have hvpair := pairwise_disjoint_of_Qstat_sum_eq s v hEq
    obtain ⟨hvparts, -⟩ := parts_and_Qstat_sum_of_pairwise_disjoint s v hvpair
    have : ∑ j ∈ s, parts (f i j) = ∑ j ∈ s, parts (f i₀ j) := by
      rw [← hpartsw₀, ← hv_sum, hvparts]
      exact Finset.sum_congr rfl fun j hj => (parts_of_mem_orbit (hv_orbit j hj)).symm
    exact hne (hinj this)
  rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀) hvanish] at hcoeff
  have hne0 : MvPolynomial.coeff w₀ (∏ j ∈ s, msym R (f i₀ j)) ≠ 0 := by
    rw [coeff_prod_msym_cast]
    have := coeff_prod_msym_pos s (f i₀) u hu_orbit
    rw [← hw₀] at this
    exact Nat.cast_ne_zero.2 (by omega)
  rcases mul_eq_zero.1 hcoeff with h | h
  · exact hg₀ h
  · exact hne0 h
