-- Prove2me | solution 1 for ErdosProblems.Shared.IdealCounting.card_le_sum_countSupp
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:19:49.673294+00:00
-- url     : https://prove2.me/submissions/7582481d-1be6-4688-8e3f-6b5a21604ca2

import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Theorems.Thm_ErdosProblems_Shared_IdealCounting_card_normSet
import Theorems.Thm_ErdosProblems_Shared_IdealCounting_countSupp_eq
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



theorem mem_normSet {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ normSet n ↔ absNorm I = n := by
  simp [normSet]







/-! ### Factorisation into a `P`-part and a `¬P`-part -/



theorem normalizedFactors_prod_filter (Q : Ideal (𝓞 K) → Prop) [DecidablePred Q]
    (I : Ideal (𝓞 K)) :
    normalizedFactors ((normalizedFactors I).filter Q).prod = (normalizedFactors I).filter Q :=
  normalizedFactors_prod_of_prime fun 𝔭 h𝔭 =>
    prime_of_normalized_factor 𝔭 (Multiset.mem_of_mem_filter h𝔭)
end ErdosProblems.Shared.IdealCounting

open NumberField UniqueFactorizationMonoid Ideal
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.IdealCounting in
theorem solution (P : Ideal (𝓞 K) → Prop) {n : ℕ} (hn : n ≠ 0) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = n} ≤
      ∑ x ∈ n.divisorsAntidiagonal, countSupp K P x.1 * countSupp K (fun 𝔭 => ¬ P 𝔭) x.2 := by
  classical
  let gp : Ideal (𝓞 K) → Ideal (𝓞 K) := fun I => ((normalizedFactors I).filter P).prod
  let bp : Ideal (𝓞 K) → Ideal (𝓞 K) := fun I =>
    ((normalizedFactors I).filter (fun 𝔭 => ¬ P 𝔭)).prod
  have hgb : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → gp I * bp I = I := fun I hI => by
    simp only [gp, bp]
    rw [Multiset.prod_filter_mul_prod_filter_not, Ideal.prod_normalizedFactors_eq_self hI]
  have hS0 : ∀ I ∈ normSet (K := K) n, I ≠ ⊥ := fun I hI h => by
    apply hn
    rw [← mem_normSet.mp hI, h, absNorm_bot]
  let f : Ideal (𝓞 K) → ℕ × ℕ := fun I => (absNorm (gp I), absNorm (bp I))
  have hmaps : ((normSet (K := K) n : Finset (Ideal (𝓞 K))) : Set (Ideal (𝓞 K))).MapsTo f
      (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    intro I hI
    simp only [Finset.mem_coe, Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, hn⟩
    show absNorm (gp I) * absNorm (bp I) = n
    rw [← map_mul, hgb I (hS0 I hI)]
    exact mem_normSet.mp hI
  rw [card_normSet, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [countSupp_eq, countSupp_eq, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun I => (gp I, bp I)) ?_ ?_
  · intro I hI
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hI
    obtain ⟨-, hfx⟩ := hI
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Set.mem_setOf_eq,
      mem_normSet]
    refine ⟨⟨congrArg Prod.fst hfx, ?_⟩, ⟨congrArg Prod.snd hfx, ?_⟩⟩
    · intro 𝔭 h𝔭
      simp only [gp] at h𝔭
      rw [normalizedFactors_prod_filter] at h𝔭
      exact Multiset.of_mem_filter h𝔭
    · intro 𝔭 h𝔭
      simp only [bp] at h𝔭
      rw [normalizedFactors_prod_filter] at h𝔭
      exact (Multiset.mem_filter.mp h𝔭).2
  · intro I hI J hJ hIJ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hI hJ
    have h1 : gp I = gp J := congrArg Prod.fst hIJ
    have h2 : bp I = bp J := congrArg Prod.snd hIJ
    rw [← hgb I (hS0 I hI.1), ← hgb J (hS0 J hJ.1), h1, h2]
