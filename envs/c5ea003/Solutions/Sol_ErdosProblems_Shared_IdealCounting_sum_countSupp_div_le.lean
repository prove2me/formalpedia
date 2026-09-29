-- Prove2me | solution 1 for ErdosProblems.Shared.IdealCounting.sum_countSupp_div_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:33:44.900163+00:00
-- url     : https://prove2.me/submissions/7399404b-898e-438a-be1a-8ab1c4e70264

import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Theorems.Thm_ErdosProblems_Shared_IdealCounting_exists_bound_sum_inv_absNorm
import Theorems.Thm_ErdosProblems_Shared_IdealCounting_sum_inv_absNorm_le_prod
import Mathlib.Analysis.PSeries
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int

/-!
# Counting ideals by their prime factors in a number field

For a number field `K` and a predicate `P` on ideals of `𝓞 K`, `countSupp K P n` is the
number of ideals of absolute norm `n` all of whose prime factors satisfy `P`.  This file
proves the three coefficientwise facts that feed the pole comparison of
`ErdosProblems.Shared.DirichletPole`:

* `card_le_sum_countSupp` (**factorisation into two parts**): every ideal of norm `n` is the
  product of its `P`-part and its `¬P`-part, so the number of ideals of norm `n` is at most the
  Dirichlet convolution of the two restricted counts;
* `sum_countSupp_div_le` (**the bad part converges at `s = 1`**): when `P 𝔭` says that the
  norm of `𝔭` is a prime larger than `N₀`, the series `∑ countSupp K (¬P) n / n` has bounded
  partial sums.  The primes excluded are finitely many primes of small norm and primes of
  norm `p ^ f` with `f ≥ 2`; at most `[K : ℚ]` primes lie over each `p`, so their
  reciprocal norms are dominated by `[K : ℚ] ∑ 1 / p²`, and a finite Euler product over the
  primes involved bounds the whole series;
* `sum_countSupp_mul_le` (**split primes double the count**): if every prime `𝔭` with `P 𝔭`
  has two distinct primes of an extension `M` above it, each of the same norm as `𝔭`, then
  the Dirichlet convolution of the `P`-count with itself is at most the number of ideals of
  `𝓞 M` of norm `n`.  The injection sends a pair of ideals `(I, J)` to the product of the
  first lifts of the prime factors of `I` and the second lifts of those of `J`.
-/

noncomputable section

namespace ErdosProblems.Shared.IdealCounting
open NumberField UniqueFactorizationMonoid Ideal

variable (K : Type*) [Field K] [NumberField K]



theorem natCard_eq_card_filter {α : Type*} (S : Finset α) (p : α → Prop) [DecidablePred p]
    (h : ∀ x, p x → x ∈ S) : Nat.card {x // p x} = (S.filter p).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [Finset.mem_filter]
    exact ⟨fun hx => ⟨h x hx, hx⟩, fun hx => hx.2⟩)

variable {K}











/-! ### Factorisation into a `P`-part and a `¬P`-part -/

theorem prime_of_mem_normalizedFactors {I 𝔭 : Ideal (𝓞 K)} (h : 𝔭 ∈ normalizedFactors I) :
    𝔭.IsPrime ∧ 𝔭 ≠ ⊥ :=
  ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor 𝔭 h),
    (prime_of_normalized_factor 𝔭 h).ne_zero⟩





/-! ### Split primes: the convolution of the `P`-count with itself -/



/-! ### A finite Euler product bound -/



theorem inv_one_sub_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have h1x : 0 < 1 - x := by linarith
  calc (1 - x)⁻¹ ≤ 2 * x + 1 := by
        rw [← one_div, div_le_iff₀ h1x]
        nlinarith
    _ ≤ Real.exp (2 * x) := Real.add_one_le_exp _

theorem prod_inv_one_sub_le_exp (F : Finset (Ideal (𝓞 K))) (hF : ∀ 𝔭 ∈ F, 2 ≤ absNorm 𝔭) :
    ∏ 𝔭 ∈ F, (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹ ≤
      Real.exp (2 * ∑ 𝔭 ∈ F, ((absNorm 𝔭 : ℝ))⁻¹) := by
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro 𝔭 h𝔭
    have h2 : (2 : ℝ) ≤ absNorm 𝔭 := by exact_mod_cast hF 𝔭 h𝔭
    have hx1 : ((absNorm 𝔭 : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    exact inv_nonneg.mpr (by linarith)
  · intro 𝔭 h𝔭
    have h2 : (2 : ℝ) ≤ absNorm 𝔭 := by exact_mod_cast hF 𝔭 h𝔭
    apply inv_one_sub_le_exp (inv_nonneg.mpr (Nat.cast_nonneg _))
    rw [one_div]
    exact inv_anti₀ (by norm_num) h2

/-! ### Primes of non-prime norm -/
end ErdosProblems.Shared.IdealCounting

open NumberField UniqueFactorizationMonoid Ideal
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.IdealCounting in
theorem solution (N₀ : ℕ) :
    ∃ B : ℝ, ∀ X : ℕ, ∑ n ∈ Finset.range X,
      (countSupp K (fun 𝔭 => ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) n : ℝ) / n ≤ B := by
  classical
  obtain ⟨C, hC⟩ := exists_bound_sum_inv_absNorm (K := K) N₀
  refine ⟨Real.exp (2 * C), fun X => ?_⟩
  have hfinT : {I : Ideal (𝓞 K) | absNorm I < X ∧ I ≠ ⊥ ∧
      ∀ 𝔭 ∈ normalizedFactors I, ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)}.Finite :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) X).subset fun I hI => le_of_lt hI.1
  set T := hfinT.toFinset with hT
  have hmemT : ∀ I, I ∈ T ↔ absNorm I < X ∧ I ≠ ⊥ ∧
      ∀ 𝔭 ∈ normalizedFactors I, ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) := fun I => by
    rw [hT, Set.Finite.mem_toFinset]
    rfl
  have hsumT : ∑ n ∈ Finset.range X,
      (countSupp K (fun 𝔭 => ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) n : ℝ) / n =
        ∑ I ∈ T, ((absNorm I : ℝ))⁻¹ := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := Finset.range X)
      (g := fun I => absNorm I) (fun I hI => Finset.mem_range.mpr ((hmemT I).mp hI).1)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => ((n : ℝ))⁻¹)
      (fun I hI => by rw [(Finset.mem_filter.mp hI).2]), Finset.sum_const, nsmul_eq_mul,
      div_eq_mul_inv]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    congr 1
    have hcard := natCard_eq_card_filter T
      (fun I : Ideal (𝓞 K) => absNorm I = n ∧
        ∀ 𝔭 ∈ normalizedFactors I, ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭))
      (fun I hI => by
        refine (hmemT I).mpr ⟨?_, ?_, hI.2⟩
        · rw [hI.1]
          exact Finset.mem_range.mp ‹n ∈ Finset.range X›
        · intro h
          apply hn
          rw [← hI.1, h, absNorm_bot])
    have hfilt : T.filter (fun I : Ideal (𝓞 K) => absNorm I = n ∧
        ∀ 𝔭 ∈ normalizedFactors I, ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) =
        T.filter (fun I => absNorm I = n) := by
      ext I
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2, ((hmemT I).mp h1).2.2⟩
    rw [hfilt] at hcard
    unfold countSupp
    exact_mod_cast hcard
  rw [hsumT]
  have hTprop : ∀ I ∈ T, I ≠ ⊥ ∧
      ∀ 𝔭 ∈ normalizedFactors I, ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) :=
    fun I hI => ((hmemT I).mp hI).2
  let F : Finset (Ideal (𝓞 K)) := T.biUnion fun I => (normalizedFactors I).toFinset
  have hF : ∀ 𝔭 ∈ F, 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) := by
    intro 𝔭 h𝔭
    obtain ⟨I, hI, h𝔭I⟩ := Finset.mem_biUnion.mp h𝔭
    rw [Multiset.mem_toFinset] at h𝔭I
    exact ⟨(prime_of_mem_normalizedFactors h𝔭I).1, (prime_of_mem_normalizedFactors h𝔭I).2,
      (hTprop I hI).2 𝔭 h𝔭I⟩
  have hF2 : ∀ 𝔭 ∈ F, 2 ≤ absNorm 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨hprime, hbot, -⟩ := hF 𝔭 h𝔭
    have h0 : absNorm 𝔭 ≠ 0 := by rw [Ne, absNorm_eq_zero_iff]; exact hbot
    have h1 : absNorm 𝔭 ≠ 1 := by rw [Ne, absNorm_eq_one_iff]; exact hprime.ne_top
    omega
  calc ∑ I ∈ T, ((absNorm I : ℝ))⁻¹
      ≤ ∏ 𝔭 ∈ F, (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹ := by
        refine sum_inv_absNorm_le_prod F hF2 T fun I hI => ⟨(hTprop I hI).1, fun 𝔭 h𝔭 => ?_⟩
        exact Finset.mem_biUnion.mpr ⟨I, hI, Multiset.mem_toFinset.mpr h𝔭⟩
    _ ≤ Real.exp (2 * ∑ 𝔭 ∈ F, ((absNorm 𝔭 : ℝ))⁻¹) := prod_inv_one_sub_le_exp F hF2
    _ ≤ Real.exp (2 * C) := by
        apply Real.exp_le_exp.mpr
        have := hC F hF
        linarith
