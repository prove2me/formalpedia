-- Prove2me | solution 1 for ErdosProblems.Shared.IdealCounting.exists_bound_sum_inv_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:31:00.546049+00:00
-- url     : https://prove2.me/submissions/4c1be289-adb2-4cb7-9ddb-df81af69378b

import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
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





variable {K}











/-! ### Factorisation into a `P`-part and a `¬P`-part -/







/-! ### Split primes: the convolution of the `P`-count with itself -/



/-! ### A finite Euler product bound -/







/-! ### Primes of non-prime norm -/

theorem exists_prime_pow_absNorm {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥) :
    ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ absNorm 𝔭 = p ^ k ∧ (p : 𝓞 K) ∈ 𝔭 := by
  haveI : 𝔭.IsMaximal := hp.isMaximal h0
  letI : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have hne : absNorm 𝔭 ≠ 0 := by rwa [Ne, absNorm_eq_zero_iff]
  haveI hfin : Finite (𝓞 K ⧸ 𝔭) := (absNorm_ne_zero_iff 𝔭).mp hne
  letI : Fintype (𝓞 K ⧸ 𝔭) := Fintype.ofFinite _
  obtain ⟨k, hpr, hcard⟩ := FiniteField.card (𝓞 K ⧸ 𝔭) (ringChar (𝓞 K ⧸ 𝔭))
  refine ⟨ringChar (𝓞 K ⧸ 𝔭), k, hpr, k.pos, ?_, ?_⟩
  · rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar

theorem card_le_finrank_of_forall_mem {p : ℕ} (hp : p.Prime) (F : Finset (Ideal (𝓞 K)))
    (hF : ∀ 𝔭 ∈ F, 𝔭.IsPrime ∧ (p : 𝓞 K) ∈ 𝔭) : F.card ≤ Module.finrank ℚ K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  calc F.card ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card := by
        apply Finset.card_le_card
        intro 𝔭 h𝔭
        obtain ⟨hprime, hmem⟩ := hF 𝔭 h𝔭
        rw [IsDedekindDomain.mem_primesOverFinset_iff hp0]
        refine ⟨hprime, ⟨?_⟩⟩
        refine (Int.ideal_span_isMaximal_of_prime p).eq_of_le ?_ ?_
        · haveI := hprime
          exact Ideal.IsPrime.ne_top (Ideal.IsPrime.comap (algebraMap ℤ (𝓞 K)))
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          simpa using hmem
    _ ≤ Module.finrank ℚ K := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hp0
end ErdosProblems.Shared.IdealCounting

open NumberField UniqueFactorizationMonoid Ideal
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.IdealCounting in
theorem solution (N₀ : ℕ) :
    ∃ C : ℝ, ∀ F : Finset (Ideal (𝓞 K)),
      (∀ 𝔭 ∈ F, 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) →
        ∑ 𝔭 ∈ F, ((absNorm 𝔭 : ℝ))⁻¹ ≤ C := by
  classical
  set F₀ := (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N₀).toFinset with hF₀
  have hsumm : Summable (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr one_lt_two
  refine ⟨F₀.card + Module.finrank ℚ K * ∑' m : ℕ, ((m : ℝ) ^ 2)⁻¹, ?_⟩
  intro F hF
  rw [← Finset.sum_filter_add_sum_filter_not F (fun 𝔭 => absNorm 𝔭 ≤ N₀)]
  have hone : ∀ 𝔭 ∈ F, (1 : ℝ) ≤ absNorm 𝔭 := by
    intro 𝔭 h𝔭
    have h0 : absNorm 𝔭 ≠ 0 := by rw [Ne, absNorm_eq_zero_iff]; exact (hF 𝔭 h𝔭).2.1
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  refine add_le_add ?_ ?_
  · calc ∑ 𝔭 ∈ F.filter (fun 𝔭 => absNorm 𝔭 ≤ N₀), ((absNorm 𝔭 : ℝ))⁻¹
        ≤ ∑ 𝔭 ∈ F.filter (fun 𝔭 => absNorm 𝔭 ≤ N₀), (1 : ℝ) := by
          refine Finset.sum_le_sum fun 𝔭 h𝔭 => ?_
          exact inv_le_one_of_one_le₀ (hone 𝔭 (Finset.mem_of_mem_filter 𝔭 h𝔭))
      _ = ((F.filter (fun 𝔭 => absNorm 𝔭 ≤ N₀)).card : ℝ) := by simp
      _ ≤ F₀.card := by
          apply Nat.cast_le.mpr
          apply Finset.card_le_card
          intro 𝔭 h𝔭
          rw [hF₀, Set.Finite.mem_toFinset]
          exact (Finset.mem_filter.mp h𝔭).2
  · set F₂ := F.filter (fun 𝔭 => ¬ absNorm 𝔭 ≤ N₀) with hF₂
    let q : Ideal (𝓞 K) → ℕ := fun 𝔭 => (absNorm 𝔭).minFac
    have hq : ∀ 𝔭 ∈ F₂, (q 𝔭).Prime ∧ ((q 𝔭 : ℕ) : 𝓞 K) ∈ 𝔭 ∧ (q 𝔭) ^ 2 ≤ absNorm 𝔭 := by
      intro 𝔭 h𝔭
      obtain ⟨h𝔭F, hbig⟩ := Finset.mem_filter.mp h𝔭
      obtain ⟨hprime, hbot, hbad⟩ := hF 𝔭 h𝔭F
      have hnotprime : ¬ Nat.Prime (absNorm 𝔭) := fun h => hbad ⟨h, not_le.mp hbig⟩
      obtain ⟨p, k, hp, hk, hnorm, hmem⟩ := exists_prime_pow_absNorm hprime hbot
      have hqp : q 𝔭 = p := by
        simp only [q]
        rw [hnorm]
        exact Nat.Prime.pow_minFac hp hk.ne'
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk1 : k = 1 := by omega
        rw [hnorm, hk1, pow_one] at hnotprime
        exact hnotprime hp
      refine ⟨hqp ▸ hp, hqp ▸ hmem, ?_⟩
      rw [hqp, hnorm]
      exact Nat.pow_le_pow_right hp.pos hk2
    have hfib : ∀ r ∈ F₂.image q, (F₂.filter (fun 𝔭 => q 𝔭 = r)).card ≤ Module.finrank ℚ K := by
      intro r hr
      obtain ⟨𝔭₀, h𝔭₀, rfl⟩ := Finset.mem_image.mp hr
      apply card_le_finrank_of_forall_mem (hq 𝔭₀ h𝔭₀).1
      intro 𝔭 h𝔭
      obtain ⟨h𝔭F₂, hqe⟩ := Finset.mem_filter.mp h𝔭
      refine ⟨(hF 𝔭 (Finset.mem_of_mem_filter 𝔭 h𝔭F₂)).1, ?_⟩
      rw [← hqe]
      exact (hq 𝔭 h𝔭F₂).2.1
    calc ∑ 𝔭 ∈ F₂, ((absNorm 𝔭 : ℝ))⁻¹
        ≤ ∑ 𝔭 ∈ F₂, (((q 𝔭 : ℕ) : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun 𝔭 h𝔭 => ?_
          have hq2 := (hq 𝔭 h𝔭).2.2
          have hqpos : (0 : ℝ) < ((q 𝔭 : ℕ) : ℝ) ^ 2 := by
            have := (hq 𝔭 h𝔭).1.pos
            positivity
          exact inv_anti₀ hqpos (by exact_mod_cast hq2)
      _ = ∑ r ∈ F₂.image q, ∑ 𝔭 ∈ F₂.filter (fun 𝔭 => q 𝔭 = r), (((q 𝔭 : ℕ) : ℝ) ^ 2)⁻¹ :=
          (Finset.sum_fiberwise_of_maps_to (fun 𝔭 h𝔭 => Finset.mem_image_of_mem q h𝔭) _).symm
      _ = ∑ r ∈ F₂.image q, ((F₂.filter (fun 𝔭 => q 𝔭 = r)).card : ℝ) * (((r : ℕ) : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_congr rfl (g := fun _ => (((r : ℕ) : ℝ) ^ 2)⁻¹)]
          · rw [Finset.sum_const, nsmul_eq_mul]
          · intro 𝔭 h𝔭
            rw [(Finset.mem_filter.mp h𝔭).2]
      _ ≤ ∑ r ∈ F₂.image q, (Module.finrank ℚ K : ℝ) * (((r : ℕ) : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun r hr => ?_
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (by positivity))
          exact_mod_cast hfib r hr
      _ = (Module.finrank ℚ K : ℝ) * ∑ r ∈ F₂.image q, (((r : ℕ) : ℝ) ^ 2)⁻¹ :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, ((m : ℝ) ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact Summable.sum_le_tsum _ (fun m _ => inv_nonneg.mpr (by positivity)) hsumm
