-- Prove2me | solution 1 for ErdosProblems.Shared.IdealCounting.sum_countSupp_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:31:01.846733+00:00
-- url     : https://prove2.me/submissions/b0a00720-118c-4dff-890b-9e2e5802dc1d

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

theorem prime_of_mem_normalizedFactors {I 𝔭 : Ideal (𝓞 K)} (h : 𝔭 ∈ normalizedFactors I) :
    𝔭.IsPrime ∧ 𝔭 ≠ ⊥ :=
  ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor 𝔭 h),
    (prime_of_normalized_factor 𝔭 h).ne_zero⟩





/-! ### Split primes: the convolution of the `P`-count with itself -/
end ErdosProblems.Shared.IdealCounting

open NumberField UniqueFactorizationMonoid Ideal
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.IdealCounting in
theorem solution (M : Type*) [Field M] [NumberField M] [Algebra K M]
    (P : Ideal (𝓞 K) → Prop)
    (hsplit : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → P 𝔭 →
      ∃ Q₁ Q₂ : Ideal (𝓞 M), Q₁.IsPrime ∧ Q₁ ≠ ⊥ ∧ Q₂.IsPrime ∧ Q₂ ≠ ⊥ ∧
        absNorm Q₁ = absNorm 𝔭 ∧ absNorm Q₂ = absNorm 𝔭 ∧
        Q₁.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧ Q₂.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧
        Q₁ ≠ Q₂)
    {n : ℕ} (hn : n ≠ 0) :
    ∑ x ∈ n.divisorsAntidiagonal, countSupp K P x.1 * countSupp K P x.2 ≤
      Nat.card {Q : Ideal (𝓞 M) // absNorm Q = n} := by
  classical
  choose! L₁ L₂ hL using hsplit
  set ι := algebraMap (𝓞 K) (𝓞 M) with hι
  -- goodness of an ideal
  let good : Ideal (𝓞 K) → Prop := fun I => ∀ 𝔭 ∈ normalizedFactors I, P 𝔭
  have hgoodL : ∀ I : Ideal (𝓞 K), good I → ∀ 𝔭 ∈ normalizedFactors I,
      (L₁ 𝔭).IsPrime ∧ L₁ 𝔭 ≠ ⊥ ∧ (L₂ 𝔭).IsPrime ∧ L₂ 𝔭 ≠ ⊥ ∧
        absNorm (L₁ 𝔭) = absNorm 𝔭 ∧ absNorm (L₂ 𝔭) = absNorm 𝔭 ∧
        (L₁ 𝔭).comap ι = 𝔭 ∧ (L₂ 𝔭).comap ι = 𝔭 ∧ L₁ 𝔭 ≠ L₂ 𝔭 := fun I hI 𝔭 h𝔭 =>
    hL 𝔭 (prime_of_mem_normalizedFactors h𝔭).1 (prime_of_mem_normalizedFactors h𝔭).2 (hI 𝔭 h𝔭)
  let X : Ideal (𝓞 K) × Ideal (𝓞 K) → Multiset (Ideal (𝓞 M)) := fun p =>
    (normalizedFactors p.1).map L₁ + (normalizedFactors p.2).map L₂
  let Φ : Ideal (𝓞 K) × Ideal (𝓞 K) → Ideal (𝓞 M) := fun p => (X p).prod
  have hXprime : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), good p.1 → good p.2 →
      ∀ Q ∈ X p, Prime Q := by
    intro p h1 h2 Q hQ
    simp only [X, Multiset.mem_add, Multiset.mem_map] at hQ
    rcases hQ with ⟨𝔭, h𝔭, rfl⟩ | ⟨𝔭, h𝔭, rfl⟩
    · obtain ⟨hp, hb, -⟩ := hgoodL _ h1 𝔭 h𝔭
      exact Ideal.prime_of_isPrime hb hp
    · obtain ⟨-, -, hp, hb, -⟩ := hgoodL _ h2 𝔭 h𝔭
      exact Ideal.prime_of_isPrime hb hp
  have hnfΦ : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), good p.1 → good p.2 →
      normalizedFactors (Φ p) = X p := fun p h1 h2 =>
    normalizedFactors_prod_of_prime (hXprime p h1 h2)
  -- recovering the two factorisations from `X p`
  have hrec₁ : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), good p.1 → good p.2 →
      ((X p).filter (fun Q => L₁ (Q.comap ι) = Q)).map (fun Q => Q.comap ι) =
        normalizedFactors p.1 := by
    intro p h1 h2
    have e1 : ((normalizedFactors p.1).map L₁).filter (fun Q => L₁ (Q.comap ι) = Q) =
        (normalizedFactors p.1).map L₁ := by
      rw [Multiset.filter_eq_self]
      intro Q hQ
      obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hQ
      rw [(hgoodL _ h1 𝔭 h𝔭).2.2.2.2.2.2.1]
    have e2 : ((normalizedFactors p.2).map L₂).filter (fun Q => L₁ (Q.comap ι) = Q) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro Q hQ
      obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hQ
      rw [(hgoodL _ h2 𝔭 h𝔭).2.2.2.2.2.2.2.1]
      exact (hgoodL _ h2 𝔭 h𝔭).2.2.2.2.2.2.2.2
    show (((normalizedFactors p.1).map L₁ + (normalizedFactors p.2).map L₂).filter
      (fun Q => L₁ (Q.comap ι) = Q)).map (fun Q => Q.comap ι) = normalizedFactors p.1
    rw [Multiset.filter_add, e1, e2, add_zero, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (normalizedFactors p.1)]
    exact Multiset.map_congr rfl fun 𝔭 h𝔭 => (hgoodL _ h1 𝔭 h𝔭).2.2.2.2.2.2.1
  have hrec₂ : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), good p.1 → good p.2 →
      ((X p).filter (fun Q => L₂ (Q.comap ι) = Q)).map (fun Q => Q.comap ι) =
        normalizedFactors p.2 := by
    intro p h1 h2
    have e1 : ((normalizedFactors p.1).map L₁).filter (fun Q => L₂ (Q.comap ι) = Q) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro Q hQ
      obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hQ
      rw [(hgoodL _ h1 𝔭 h𝔭).2.2.2.2.2.2.1]
      exact fun h => (hgoodL _ h1 𝔭 h𝔭).2.2.2.2.2.2.2.2 h.symm
    have e2 : ((normalizedFactors p.2).map L₂).filter (fun Q => L₂ (Q.comap ι) = Q) =
        (normalizedFactors p.2).map L₂ := by
      rw [Multiset.filter_eq_self]
      intro Q hQ
      obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hQ
      rw [(hgoodL _ h2 𝔭 h𝔭).2.2.2.2.2.2.2.1]
    show (((normalizedFactors p.1).map L₁ + (normalizedFactors p.2).map L₂).filter
      (fun Q => L₂ (Q.comap ι) = Q)).map (fun Q => Q.comap ι) = normalizedFactors p.2
    rw [Multiset.filter_add, e1, e2, zero_add, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (normalizedFactors p.2)]
    exact Multiset.map_congr rfl fun 𝔭 h𝔭 => (hgoodL _ h2 𝔭 h𝔭).2.2.2.2.2.2.2.1
  -- the norm of `Φ p`
  have hnormΦ : ∀ p : Ideal (𝓞 K) × Ideal (𝓞 K), good p.1 → good p.2 → p.1 ≠ ⊥ → p.2 ≠ ⊥ →
      absNorm (Φ p) = absNorm p.1 * absNorm p.2 := by
    intro p h1 h2 hp1 hp2
    simp only [Φ, X]
    rw [Multiset.prod_add, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map,
      Multiset.map_map]
    conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self hp1, ← Ideal.prod_normalizedFactors_eq_self hp2,
      map_multiset_prod, map_multiset_prod]
    congr 1
    · congr 1
      refine Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_
      exact (hgoodL _ h1 𝔭 h𝔭).2.2.2.2.1
    · congr 1
      refine Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_
      exact (hgoodL _ h2 𝔭 h𝔭).2.2.2.2.2.1
  -- the finite set of good pairs
  let G : ℕ → Finset (Ideal (𝓞 K)) := fun m =>
    (normSet (K := K) m).filter (fun I => ∀ 𝔭 ∈ normalizedFactors I, P 𝔭)
  let U : Finset (Ideal (𝓞 K) × Ideal (𝓞 K)) :=
    n.divisorsAntidiagonal.biUnion fun x => G x.1 ×ˢ G x.2
  have hU : ∀ p ∈ U, good p.1 ∧ good p.2 ∧ absNorm p.1 * absNorm p.2 = n := by
    intro p hp
    simp only [U, Finset.mem_biUnion, Finset.mem_product, G, Finset.mem_filter,
      mem_normSet] at hp
    obtain ⟨x, hx, ⟨h1, g1⟩, ⟨h2, g2⟩⟩ := hp
    refine ⟨g1, g2, ?_⟩
    rw [h1, h2]
    exact (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hU0 : ∀ p ∈ U, p.1 ≠ ⊥ ∧ p.2 ≠ ⊥ := by
    intro p hp
    obtain ⟨-, -, hnorm⟩ := hU p hp
    constructor
    · intro h
      apply hn
      rw [← hnorm, h, absNorm_bot, zero_mul]
    · intro h
      apply hn
      rw [← hnorm, h, absNorm_bot, mul_zero]
  have hcardU : U.card = ∑ x ∈ n.divisorsAntidiagonal, countSupp K P x.1 * countSupp K P x.2 := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.card_product, countSupp_eq, countSupp_eq]
    · intro x _ y _ hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hpx hpy
      simp only [Finset.mem_product, G, Finset.mem_filter, mem_normSet] at hpx hpy
      apply hxy
      exact Prod.ext (hpx.1.1.symm.trans hpy.1.1) (hpx.2.1.symm.trans hpy.2.1)
  rw [← hcardU, card_normSet]
  refine Finset.card_le_card_of_injOn Φ ?_ ?_
  · intro p hp
    have hp' : p ∈ U := hp
    obtain ⟨g1, g2, hnorm⟩ := hU p hp'
    obtain ⟨hb1, hb2⟩ := hU0 p hp'
    simp only [Finset.mem_coe, mem_normSet]
    rw [hnormΦ p g1 g2 hb1 hb2, hnorm]
  · intro p hp q hq hpq
    have hp' : p ∈ U := hp
    have hq' : q ∈ U := hq
    obtain ⟨gp1, gp2, -⟩ := hU p hp'
    obtain ⟨gq1, gq2, -⟩ := hU q hq'
    obtain ⟨hp1, hp2⟩ := hU0 p hp'
    obtain ⟨hq1, hq2⟩ := hU0 q hq'
    have hX : X p = X q := by
      rw [← hnfΦ p gp1 gp2, ← hnfΦ q gq1 gq2]
      exact congrArg normalizedFactors hpq
    have e1 : normalizedFactors p.1 = normalizedFactors q.1 := by
      rw [← hrec₁ p gp1 gp2, ← hrec₁ q gq1 gq2, hX]
    have e2 : normalizedFactors p.2 = normalizedFactors q.2 := by
      rw [← hrec₂ p gp1 gp2, ← hrec₂ q gq1 gq2, hX]
    refine Prod.ext ?_ ?_
    · rw [← Ideal.prod_normalizedFactors_eq_self hp1, ← Ideal.prod_normalizedFactors_eq_self hq1, e1]
    · rw [← Ideal.prod_normalizedFactors_eq_self hp2, ← Ideal.prod_normalizedFactors_eq_self hq2, e2]
