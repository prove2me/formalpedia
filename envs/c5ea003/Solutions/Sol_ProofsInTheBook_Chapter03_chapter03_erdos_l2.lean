-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.chapter03_erdos_l2
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:26:29.223988+00:00
-- url     : https://prove2.me/submissions/315bae8f-4487-47a5-8dc9-daaab7103a5b

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03


/-!
# Chapter 3: Binomial coefficients are (almost) never powers

From "Proofs from THE BOOK" (Aigner & Ziegler).

## Book content summary

The book states Sylvester's theorem (1892):

> If n ≥ 2k, then at least one of the numbers n, n - 1, ..., n - k + 1
> has a prime divisor p greater than k.

Equivalently, the binomial coefficient C(n,k) = n(n-1)...(n-k+1)/k!
always has a prime factor p > k when n ≥ 2k.

The central case n = 2k is precisely Bertrand's postulate (Chapter 2).

For the general case, the book notes (p. 13):

> In 1934, Erdős gave a short and elementary Book Proof of Sylvester's
> result, running along the lines of his proof of Bertrand's postulate.

The book does **not** reproduce this proof in full. It references:

> P. Erdős: A theorem of Sylvester and Schur,
> J. London Math. Soc. 9 (1934), 282-288.

The rest of Chapter 3 uses Sylvester's theorem as a lemma to prove the
"binomial coefficients are almost never powers" result.

## Formalization status

The central case (C(2k,k)) is fully proved below using Bertrand's postulate.

The general case (`sylvester_general`) currently takes `hsmooth` (that
n.descFactorial k is not (k+1)-smooth) as a premise. Eliminating this
premise requires a full formalization of Erdős's 1934 Sylvester-Schur
proof, which uses a refined analysis of how prime powers are distributed
among the k consecutive integers — more delicate than the Bertrand
chapter's global inequality bounding.

This is tracked in TODO.md as "Ch03: Sylvester smoothness core" —
difficulty: Medium-Hard, blocker: needs Erdős 1934 proof formalized.
-/

namespace ProofsInTheBook.Chapter03

open Nat









theorem primorial_eq_mul_primeIntervalProduct {a M : ℕ} (haM : a ≤ M) :
    primorial M = primorial a * primeIntervalProduct a M := by
  rw [primorial, primeIntervalProduct]
  rw [show (Finset.range (M + 1)).filter Nat.Prime =
      (Finset.range (a + 1)).filter Nat.Prime ∪ (Finset.Ioc a M).filter Nat.Prime by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpM, hpprime⟩
      by_cases hpa : p ≤ a
      · exact Or.inl ⟨by omega, hpprime⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hpprime⟩
    · rintro (⟨hpa, hpprime⟩ | ⟨⟨hpa, hpM⟩, hpprime⟩) <;> exact ⟨by omega, hpprime⟩]
  rw [Finset.prod_union]
  · rfl
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp1 hp2
    omega

theorem log_primeIntervalProduct_eq_theta_sub {a M : ℕ} (haM : a ≤ M) :
    Real.log (primeIntervalProduct a M) =
      Chebyshev.theta (M : ℝ) - Chebyshev.theta (a : ℝ) := by
  have hprod := primorial_eq_mul_primeIntervalProduct (a := a) (M := M) haM
  have hposA : 0 < (primorial a : ℕ) := primorial_pos a
  have hposP : 0 < primeIntervalProduct a M := by
    dsimp [primeIntervalProduct]
    exact Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos
  have hlogprod :
      Real.log (primorial M) =
        Real.log (primorial a) + Real.log (primeIntervalProduct a M) := by
    rw [hprod, Nat.cast_mul]
    exact Real.log_mul
      (by exact_mod_cast hposA.ne' : ((primorial a : ℕ) : ℝ) ≠ 0)
      (by exact_mod_cast hposP.ne' : ((primeIntervalProduct a M : ℕ) : ℝ) ≠ 0)
  rw [Chebyshev.theta_eq_log_primorial, Chebyshev.theta_eq_log_primorial]
  norm_num at hlogprod ⊢
  linarith

theorem log_primeIntervalProduct_le_min_third_log4_sub_theta
    {a M : ℕ} (haM : a ≤ M) :
    Real.log (primeIntervalProduct a M) ≤
      (M : ℝ) * Real.log 4 - Chebyshev.theta (a : ℝ) := by
  rw [log_primeIntervalProduct_eq_theta_sub haM]
  have hthetaM := Chebyshev.theta_le_log4_mul_x (x := (M : ℝ)) (by positivity)
  linarith

theorem primeIntervalProduct_dvd_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    primeIntervalProduct a M ∣ M.choose a := by
  rw [primeIntervalProduct, ← Nat.add_sub_of_le haM]
  exact Finset.prod_primes_dvd _ (fun _ hp => (Finset.mem_filter.1 hp).2.prime) fun p hp => by
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact hp.2.dvd_choose_add hp.1.1 (hd.trans_lt hp.1.1) hp.1.2

theorem primeIntervalProduct_le_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    primeIntervalProduct a M ≤ M.choose a := by
  exact le_of_dvd (Nat.choose_pos haM) (primeIntervalProduct_dvd_choose haM hd)

theorem log_primeIntervalProduct_le_log_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    Real.log (primeIntervalProduct a M) ≤ Real.log (M.choose a) := by
  exact Real.log_le_log
    (by exact_mod_cast (Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos :
      0 < primeIntervalProduct a M))
    (by exact_mod_cast primeIntervalProduct_le_choose haM hd)

theorem sqrt_le_div_three_of_nine_le {n : ℕ} (hn : 9 ≤ n) : sqrt n ≤ n / 3 := by
  rw [← Nat.lt_succ_iff]
  rw [Nat.sqrt_lt]
  have hq : 3 ≤ n / 3 := by omega
  have hnle : n ≤ 3 * (n / 3) + 2 := by omega
  nlinarith [sq_nonneg ((n / 3 : ℕ) : ℤ)]

theorem sqrt_le_min_of_nine_le_and_lt_sq {n k : ℕ} (hn : 9 ≤ n) (hlt : n < k * k) :
    sqrt n ≤ min k (n / 3) := by
  refine le_min ?_ (sqrt_le_div_three_of_nine_le hn)
  exact (Nat.sqrt_lt.mpr hlt).le

theorem not_hasPrimeFactorAbove_iff_noLargePrimeFactor {k m : ℕ} :
    ¬ HasPrimeFactorAbove k m ↔ NoLargePrimeFactor k m := by
  constructor
  · intro h p hp hpdvd
    by_contra hkp
    exact h ⟨p, by omega, hp, hpdvd⟩
  · rintro h ⟨p, hkp, hp, hpdvd⟩
    exact (not_lt_of_ge (h p hp hpdvd)) hkp

theorem factorization_choose_eq_zero_of_noLargePrimeFactor
    {n k p : ℕ} (hno : NoLargePrimeFactor k (n.choose k)) (hkp : k < p) :
    (n.choose k).factorization p = 0 := by
  by_cases hp : p.Prime
  · by_contra hne
    have hpdvd : p ∣ n.choose k := Nat.dvd_of_factorization_pos hne
    exact (not_lt_of_ge (hno p hp hpdvd)) hkp
  · exact Nat.factorization_eq_zero_of_not_prime (n.choose k) hp

theorem Finset.prod_le_pow_card_of_le {α : Type*} (s : Finset α) (f : α → ℕ) (N : ℕ)
    (h : ∀ a ∈ s, f a ≤ N) : (∏ a ∈ s, f a) ≤ N ^ s.card := by
  classical
  calc
    (∏ a ∈ s, f a) ≤ ∏ _a ∈ s, N := Finset.prod_le_prod' h
    _ = N ^ s.card := by rw [Finset.prod_const]

theorem choose_le_pow_primeCounting_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k ≤ n ^ Nat.primeCounting k := by
  classical
  let s := (Finset.range (n + 1)).filter (fun p => p ∈ Nat.primesLE k)
  have hprod_filter :
      (∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p)
        = ∏ p ∈ s, p ^ (n.choose k).factorization p := by
    symm
    refine Finset.prod_subset (Finset.filter_subset _ _) ?_
    intro p hp_range hp_not_s
    have hp_not_primes : p ∉ Nat.primesLE k := by
      intro hp_primes
      exact hp_not_s (Finset.mem_filter.mpr ⟨hp_range, hp_primes⟩)
    have hfac : (n.choose k).factorization p = 0 := by
      by_cases hpprime : p.Prime
      · have hkp : k < p := by
          by_contra hnot
          exact hp_not_primes (Nat.mem_primesLE.mpr ⟨le_of_not_gt hnot, hpprime⟩)
        exact factorization_choose_eq_zero_of_noLargePrimeFactor hno hkp
      · exact Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime
    simp [hfac]
  have hprod_le : (∏ p ∈ s, p ^ (n.choose k).factorization p) ≤ n ^ s.card :=
    Finset.prod_le_pow_card_of_le s (fun p => p ^ (n.choose k).factorization p) n
      (fun p _ => Nat.pow_factorization_choose_le hnpos)
  have hcard : s.card ≤ (Nat.primesLE k).card := by
    refine Finset.card_le_card ?_
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hpow_card : n ^ s.card ≤ n ^ Nat.primeCounting k := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Nat.pow_le_pow_right hnpos hcard
  calc
    n.choose k = ∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p := by
      exact (Nat.prod_pow_factorization_choose n k hkn).symm
    _ = ∏ p ∈ s, p ^ (n.choose k).factorization p := hprod_filter
    _ ≤ n ^ s.card := hprod_le
    _ ≤ n ^ Nat.primeCounting k := hpow_card

theorem choose_factorization_le_min_third_of_noLargePrimeFactor
    {n k : ℕ} (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k =
      ∏ p ∈ Finset.range (min k (n / 3) + 1),
        p ^ (n.choose k).factorization p := by
  refine (Eq.trans ?_ (Nat.prod_pow_factorization_choose n k hkn)).symm
  refine Finset.prod_subset ?hsub ?hzero
  · intro p hp
    rw [Finset.mem_range] at hp ⊢
    omega
  · intro p hp_range hp_not_small
    rw [Finset.mem_range] at hp_range hp_not_small
    have hMp : min k (n / 3) < p := by omega
    by_cases hpprime : p.Prime
    · by_cases hkp : k < p
      · rw [factorization_choose_eq_zero_of_noLargePrimeFactor hno hkp, pow_zero]
      · have hpk : p ≤ k := le_of_not_gt hkp
        have hpnk : p ≤ n - k := by omega
        have hp2 : p ≠ 2 := by
          intro hp_eq
          have hnthird : 2 ≤ n / 3 := by omega
          omega
        have hdiv : n / 3 < p := by omega
        have hnlt : n < 3 * p := by
          have := (Nat.div_lt_iff_lt_mul three_pos).mp hdiv
          simpa [mul_comm] using this
        rw [Nat.factorization_choose_of_lt_three_mul hp2 hpk hpnk hnlt, pow_zero]
    · rw [Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime, pow_zero]





theorem choose_le_primeCounting_sqrt_mul_primeIntervalProduct_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k ≤ n ^ Nat.primeCounting (sqrt n) * primeIntervalProduct (sqrt n) (min k (n / 3)) := by
  let M := min k (n / 3)
  let S := {p ∈ Finset.range (M + 1) | Nat.Prime p}
  let f := fun p => p ^ (n.choose k).factorization p
  have hprime_filter : ∏ p ∈ S, f p = ∏ p ∈ Finset.range (M + 1), f p := by
    refine Finset.prod_filter_of_ne fun p _ hpprime => ?_
    contrapose hpprime
    dsimp only [f]
    rw [Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime, pow_zero]
  rw [choose_factorization_le_min_third_of_noLargePrimeFactor hkn hn2k hn6 hno, ← hprime_filter,
    ← Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt n)]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ n)).trans ?_
    · exact Nat.pow_factorization_choose_le hnpos
    rw [Finset.prod_const]
    refine pow_right_mono₀ (Nat.succ_le_iff.mpr hnpos) ?_
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card fun p hp => by
      obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      exact Nat.mem_primesLE.mpr ⟨hpsqrt, (Finset.mem_filter.1 hpS).2⟩
  · refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 hpS).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 hpsqrt)
    change (∏ p ∈ Finset.filter (fun p => ¬p ≤ sqrt n) S, p) ≤
      ∏ p ∈ Finset.Ioc (sqrt n) M with p.Prime, p
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
    · intro p hp
      obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpRange, hpPrime⟩ := Finset.mem_filter.1 hpS
      rw [Finset.mem_range] at hpRange
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨lt_of_not_ge hpsqrt, by omega⟩, hpPrime⟩
    · intro p hp _hnot
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      exact hp.2.one_lt.le

theorem pow_mul_self_descFactorial_le_pow_mul_descFactorial {n k : ℕ} (hkn : k ≤ n) :
    n ^ k * k.descFactorial k ≤ k ^ k * n.descFactorial k := by
  have hnprod : n ^ k = ∏ _i ∈ Finset.range k, n := by
    rw [Finset.prod_const, Finset.card_range]
  have hkprod : k ^ k = ∏ _i ∈ Finset.range k, k := by
    rw [Finset.prod_const, Finset.card_range]
  rw [Nat.descFactorial_eq_prod_range k, Nat.descFactorial_eq_prod_range n,
    hnprod, hkprod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod' fun i hi => by
    rw [Finset.mem_range] at hi
    have hik : i ≤ k := le_of_lt hi
    have hki : k * i ≤ n * i := Nat.mul_le_mul_right i hkn
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib, Nat.mul_comm k n]
    exact Nat.sub_le_sub_left hki (n * k)

theorem pow_le_pow_mul_choose {n k : ℕ} (hkn : k ≤ n) :
    n ^ k ≤ k ^ k * n.choose k := by
  have h :=
    pow_mul_self_descFactorial_le_pow_mul_descFactorial (n := n) (k := k) hkn
  rw [Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose] at h
  have hcancel : k ! * n ^ k ≤ k ! * (k ^ k * n.choose k) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  exact le_of_mul_le_mul_left hcancel (Nat.factorial_pos k)





theorem log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + Real.log (primeIntervalProduct (sqrt n) (min k (n / 3))) := by
  let P := primeIntervalProduct (sqrt n) (min k (n / 3))
  have hnat :
      n.choose k ≤ n ^ Nat.primeCounting (sqrt n) * P :=
    choose_le_primeCounting_sqrt_mul_primeIntervalProduct_of_noLargePrimeFactor
      hnpos hkn hn2k hn6 hno
  have hpos_choose_nat : 0 < n.choose k := Nat.choose_pos hkn
  have hPpos : 0 < P := by
    dsimp [P, primeIntervalProduct]
    exact Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos
  have hlogle :
      Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting (sqrt n) * P) := by
    exact Real.log_le_log (by exact_mod_cast hpos_choose_nat) (by exact_mod_cast hnat)
  calc
    Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting (sqrt n) * P) := hlogle
    _ = Real.log ((n : ℝ) ^ Nat.primeCounting (sqrt n) * (P : ℝ)) := by
      norm_num [Nat.cast_pow]
    _ = (Nat.primeCounting (sqrt n) : ℝ) * Real.log n + Real.log P := by
      rw [Real.log_mul
        (pow_ne_zero _ (by exact_mod_cast hnpos.ne' : (n : ℝ) ≠ 0))
        (by exact_mod_cast hPpos.ne' : (P : ℝ) ≠ 0),
        Real.log_pow]
    _ = (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + Real.log (primeIntervalProduct (sqrt n) (min k (n / 3))) := by
      simp [P]

theorem log_choose_le_primeCounting_sqrt_log_add_log_choose_min_third_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrtM : sqrt n ≤ min k (n / 3)) (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + Real.log ((min k (n / 3)).choose (sqrt n)) := by
  exact (log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
    (n := n) (k := k) hnpos hkn hn2k hn6 hno).trans
      (add_le_add_right (log_primeIntervalProduct_le_log_choose hsqrtM hMsub)
        ((Nat.primeCounting (sqrt n) : ℝ) * Real.log n))

theorem log_choose_le_primeCounting_sqrt_log_add_min_third_log_two_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrtM : sqrt n ≤ min k (n / 3)) (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 := by
  let M := min k (n / 3)
  have hupper :=
    log_choose_le_primeCounting_sqrt_log_add_log_choose_min_third_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrtM hMsub
  have hchoose_pos : 0 < M.choose (sqrt n) := Nat.choose_pos hsqrtM
  have hchoose_le : M.choose (sqrt n) ≤ 2 ^ M := Nat.choose_le_two_pow M (sqrt n)
  have hlog_choose_le :
      Real.log (M.choose (sqrt n)) ≤ Real.log (2 ^ M) := by
    exact Real.log_le_log (by exact_mod_cast hchoose_pos) (by exact_mod_cast hchoose_le)
  exact hupper.trans <| add_le_add_right
    (by
      calc
        Real.log (M.choose (sqrt n)) ≤ Real.log (2 ^ M) := hlog_choose_le
        _ = Real.log ((2 : ℝ) ^ M) := by norm_num [Nat.cast_pow]
        _ = (M : ℝ) * Real.log 2 := by rw [Real.log_pow])
    ((Nat.primeCounting (sqrt n) : ℝ) * Real.log n)

theorem mul_log_sub_mul_log_le_log_choose {n k : ℕ}
    (hkpos : 0 < k) (hkn : k ≤ n) :
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k ≤ Real.log (n.choose k) := by
  have hnpos : 0 < n := hkpos.trans_le hkn
  have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
  have hnat : n ^ k ≤ k ^ k * n.choose k := pow_le_pow_mul_choose hkn
  have hlog :
      Real.log ((n : ℝ) ^ k) ≤ Real.log ((k : ℝ) ^ k * (n.choose k : ℝ)) := by
    exact Real.log_le_log
      (pow_pos (by exact_mod_cast hnpos) k)
      (by exact_mod_cast hnat)
  calc
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k
        = Real.log ((n : ℝ) ^ k) - Real.log ((k : ℝ) ^ k) := by
          rw [Real.log_pow, Real.log_pow]
    _ ≤ Real.log ((k : ℝ) ^ k * (n.choose k : ℝ)) - Real.log ((k : ℝ) ^ k) := by
      exact sub_le_sub_right hlog _
    _ = Real.log (n.choose k) := by
      rw [Real.log_mul
        (pow_ne_zero _ (by exact_mod_cast hkpos.ne' : (k : ℝ) ≠ 0))
        (by exact_mod_cast hchoose_pos.ne')]
      ring

theorem log_factorial_le_stirling_upper {m : ℕ} (hm : m ≠ 0) :
    Real.log (m !) ≤ (m : ℝ) * Real.log m - (m : ℝ) + Real.log m / 2 + 1 := by
  have hlogseq : Real.log (Stirling.stirlingSeq m) ≤ Real.log (Stirling.stirlingSeq 1) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    exact Real.log_le_log (Stirling.stirlingSeq'_pos t)
      (Stirling.stirlingSeq'_antitone (Nat.zero_le t))
  have hformula := Stirling.log_stirlingSeq_formula m
  have hone : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one, Real.log_div, Real.log_exp]
    · rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    · positivity
    · positivity
  rw [hformula, hone] at hlogseq
  rw [Real.log_mul (x := (2 : ℝ)) (y := (m : ℝ)), Real.log_div, Real.log_exp] at hlogseq
  · nlinarith
  all_goals positivity

theorem entropy_lower_le_log_choose {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    entropyTerm n k
      + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
      + Real.log (2 * Real.pi) / 2 - 2
      ≤ Real.log (n.choose k) := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < n := hkpos.trans hklt
  have hrpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
  have hfac_nat := Nat.choose_mul_factorial_mul_factorial hkn
  have hfac : (n.choose k : ℝ) * (k ! : ℝ) * ((n - k)! : ℝ) = (n ! : ℝ) := by
    exact_mod_cast hfac_nat
  have hlogfac :
      Real.log (n !) = Real.log (n.choose k) + Real.log (k !) + Real.log ((n - k)!) := by
    rw [← hfac]
    rw [Real.log_mul
        (mul_ne_zero (by exact_mod_cast hchoose_pos.ne') (by exact_mod_cast (Nat.factorial_pos k).ne'))
        (by exact_mod_cast (Nat.factorial_pos (n - k)).ne'),
      Real.log_mul
        (by exact_mod_cast hchoose_pos.ne')
        (by exact_mod_cast (Nat.factorial_pos k).ne')]
  have hN := Stirling.le_log_factorial_stirling (show n ≠ 0 from hnpos.ne')
  have hK := log_factorial_le_stirling_upper (m := k) hkpos.ne'
  have hR := log_factorial_le_stirling_upper (m := n - k) hrpos.ne'
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    exact Nat.cast_sub hkn
  rw [hlogfac] at hN
  unfold entropyTerm
  rw [hcast_sub] at hR ⊢
  nlinarith

theorem entropyTerm_lower_basic {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k
      + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ) ≤ entropyTerm n k := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (hkpos.trans hklt)
  have hrpos_nat : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hrpos : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast hrpos_nat
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    exact Nat.cast_sub hkn
  have hlog_ratio :=
    Real.log_le_sub_one_of_pos
      (x := ((n - k : ℕ) : ℝ) / (n : ℝ)) (div_pos hrpos hnpos)
  have hdiff :
      (k : ℝ) / (n : ℝ) ≤ Real.log n - Real.log (n - k) := by
    rw [Real.log_div (ne_of_gt hrpos) (ne_of_gt hnpos)] at hlog_ratio
    rw [hcast_sub] at hlog_ratio
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    field_simp [hnne] at hlog_ratio ⊢
    nlinarith
  have hmul :
      ((n - k : ℕ) : ℝ) * ((k : ℝ) / (n : ℝ)) ≤
        ((n - k : ℕ) : ℝ) * (Real.log n - Real.log (n - k)) :=
    mul_le_mul_of_nonneg_left hdiff hrpos.le
  unfold entropyTerm
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  rw [hcast_sub] at hmul ⊢
  field_simp [hnne] at hmul ⊢
  nlinarith



theorem log_choose_le_primeCounting_log_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    Real.log (n.choose k) ≤ (Nat.primeCounting k : ℝ) * Real.log n := by
  have hnat : n.choose k ≤ n ^ Nat.primeCounting k :=
    choose_le_pow_primeCounting_of_noLargePrimeFactor hnpos hkn hno
  have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
  calc
    Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting k) := by
      exact Real.log_le_log (by exact_mod_cast hchoose_pos) (by exact_mod_cast hnat)
    _ = (Nat.primeCounting k : ℝ) * Real.log n := by
      rw [show Real.log (n ^ Nat.primeCounting k) =
        Real.log ((n : ℝ) ^ Nat.primeCounting k) by norm_num [Nat.cast_pow],
        Real.log_pow]

theorem exists_large_prime_factor_choose_of_primeCounting_log_gap
    {n k : ℕ} (hkpos : 0 < k) (hnpos : 0 < n) (hkn : k ≤ n)
    (hgap :
      (Nat.primeCounting k : ℝ) * Real.log n <
        (k : ℝ) * Real.log n - (k : ℝ) * Real.log k) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hlower := mul_log_sub_mul_log_le_log_choose (n := n) (k := k) hkpos hkn
  have hupper :=
    log_choose_le_primeCounting_log_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hno
  exact not_lt_of_ge (hlower.trans hupper) hgap

theorem exists_large_prime_factor_choose_of_pow_gap
    {n k : ℕ} (hkpos : 0 < k) (hkn : k ≤ n)
    (hpi : Nat.primeCounting k ≤ k)
    (hpow : k ^ k < n ^ (k - Nat.primeCounting k)) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hnpos : 0 < n := hkpos.trans_le hkn
  refine exists_large_prime_factor_choose_of_primeCounting_log_gap
    (n := n) (k := k) hkpos hnpos hkn ?_
  have hkpow_pos : 0 < (k : ℝ) ^ k := pow_pos (by exact_mod_cast hkpos) k
  have hlogpow :
      (k : ℝ) * Real.log k <
        (k - Nat.primeCounting k : ℕ) * Real.log n := by
    have hlog : Real.log ((k : ℝ) ^ k) <
        Real.log ((n : ℝ) ^ (k - Nat.primeCounting k)) := by
      exact Real.log_lt_log hkpow_pos (by exact_mod_cast hpow)
    simpa [Real.log_pow] using hlog
  have hk_split :
      (k : ℝ) = (Nat.primeCounting k : ℝ) + (k - Nat.primeCounting k : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le hpi).symm
  calc
    (Nat.primeCounting k : ℝ) * Real.log n
        < (Nat.primeCounting k : ℝ) * Real.log n
            + (k - Nat.primeCounting k : ℕ) * Real.log n - (k : ℝ) * Real.log k := by
          linarith
    _ = ((Nat.primeCounting k : ℝ) + (k - Nat.primeCounting k : ℕ)) * Real.log n
            - (k : ℝ) * Real.log k := by
          ring
    _ = (k : ℝ) * Real.log n - (k : ℝ) * Real.log k := by
          rw [← hk_split]







theorem exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
    {n k : ℕ} (hk1 : 1 < k) (hkn : k ≤ n) (hsq : k * k ≤ n)
    (hpi : 2 * Nat.primeCounting k < k) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hkpos : 0 < k := hk1.trans' zero_lt_one
  have hnpos : 0 < n := hkpos.trans_le hkn
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hk1.trans_le hkn)
  have hlog_sq_le : Real.log ((k : ℝ) ^ 2) ≤ Real.log (n : ℝ) := by
    have hsq_pow : k ^ 2 ≤ n := by simpa [sq] using hsq
    exact Real.log_le_log (sq_pos_of_pos (by exact_mod_cast hkpos))
      (by exact_mod_cast hsq_pow)
  have htwologk_le : 2 * Real.log k ≤ Real.log n := by
    simpa [Real.log_pow] using hlog_sq_le
  have hhalf_le :
      ((k : ℝ) / 2) * Real.log n ≤ (k : ℝ) * Real.log n - (k : ℝ) * Real.log k := by
    nlinarith
  have hpi_lt_half : (Nat.primeCounting k : ℝ) < (k : ℝ) / 2 := by
    nlinarith [show (2 * Nat.primeCounting k : ℝ) < (k : ℝ) by exact_mod_cast hpi]
  have hpi_log_lt :
      (Nat.primeCounting k : ℝ) * Real.log n <
        (k : ℝ) * Real.log n - (k : ℝ) * Real.log k := by
    exact (mul_lt_mul_of_pos_right hpi_lt_half hlogn_pos).trans_le hhalf_le
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hupper :=
    log_choose_le_primeCounting_log_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hno
  have hlower := mul_log_sub_mul_log_le_log_choose (n := n) (k := k) hkpos hkn
  exact not_lt_of_ge (hlower.trans hupper) hpi_log_lt

theorem primeCounting_gap_of_120_le {k : ℕ} (hk : 120 ≤ k) :
    2 * Nat.primeCounting k < k := by
  let n := k - 30
  have hk_eq : k = 30 + n := by omega
  have hbound0 := Nat.primeCounting_add_le
    (a := 30) (k := 30) (n := n) (by norm_num) (by norm_num : 30 ≤ 30)
  have hbound : Nat.primeCounting k ≤ Nat.primeCounting 30 + Nat.totient 30 * (n / 30 + 1) := by
    simpa [hk_eq] using hbound0
  have hcalc : Nat.primeCounting 30 = 10 := by decide
  have htot : Nat.totient 30 = 8 := by decide
  have hnle : n / 30 ≤ n / 4 :=
    Nat.div_le_div_left (by norm_num : 4 ≤ 30) (by norm_num : 0 < 4)
  have hbound2 : Nat.primeCounting k ≤ 10 + 8 * (n / 30 + 1) := by
    simpa [hcalc, htot] using hbound
  have hbound3 : Nat.primeCounting k ≤ 10 + 8 * (n / 4 + 1) := by
    nlinarith
  have h4 : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
  have hdiv : 8 * (n / 4) ≤ 2 * n := by
    nlinarith
  omega



theorem primeCounting_gap_of_19_le {k : ℕ} (hk19 : 19 ≤ k) :
    2 * Nat.primeCounting k < k := by
  let n := k - 6
  have hk_eq : k = 6 + n := by omega
  have hbound0 := Nat.primeCounting_add_le
    (a := 6) (k := 6) (n := n) (by norm_num) (by norm_num : 6 ≤ 6)
  have hbound : Nat.primeCounting k ≤ Nat.primeCounting 6 + Nat.totient 6 * (n / 6 + 1) := by
    simpa [hk_eq] using hbound0
  have hcalc : Nat.primeCounting 6 = 3 := by decide
  have htot : Nat.totient 6 = 2 := by decide
  have hbound2 : Nat.primeCounting k ≤ 3 + 2 * (n / 6 + 1) := by
    simpa [hcalc, htot] using hbound
  have h6 : 6 * (n / 6) ≤ n := Nat.mul_div_le n 6
  omega

theorem primeCounting_gap_9_120_cert :
    ∀ k : Fin 120, 9 ≤ k.val → 2 * Nat.primeCounting k.val < k.val := by
  intro k hk9
  by_cases hk19 : 19 ≤ k.val
  · exact primeCounting_gap_of_19_le hk19
  · have hklt19 : k.val < 19 := by omega
    interval_cases k.val <;> decide

theorem primeCounting_gap_of_9_le_lt_120 {k : ℕ} (hk9 : 9 ≤ k) (hk120 : k < 120) :
    2 * Nat.primeCounting k < k :=
  primeCounting_gap_9_120_cert ⟨k, hk120⟩ hk9

theorem primeCounting_gap_of_9_le {k : ℕ} (hk9 : 9 ≤ k) :
    2 * Nat.primeCounting k < k := by
  by_cases hk120 : k < 120
  · exact primeCounting_gap_of_9_le_lt_120 hk9 hk120
  · exact primeCounting_gap_of_120_le (by omega)

theorem three_mul_primeCounting_le_30_150_cert :
    ∀ k : Fin 150, 33 ≤ k.val → 3 * Nat.primeCounting k.val ≤ k.val := by
  intro k hk33
  rcases le_or_gt k.val 36 with hk36 | hk37
  · have hpi : Nat.primeCounting k.val ≤ 11 := by
      have hmono := Nat.monotone_primeCounting hk36
      have h36 : Nat.primeCounting 36 = 11 := by decide
      exact hmono.trans_eq h36
    omega
  rcases le_or_gt k.val 40 with hk40 | hk41
  · have hpi : Nat.primeCounting k.val ≤ 12 := by
      have hmono := Nat.monotone_primeCounting hk40
      have h40 : Nat.primeCounting 40 = 12 := by decide
      exact hmono.trans_eq h40
    omega
  rcases le_or_gt k.val 42 with hk42 | hk43
  · have hpi : Nat.primeCounting k.val ≤ 13 := by
      have hmono := Nat.monotone_primeCounting hk42
      have h42 : Nat.primeCounting 42 = 13 := by decide
      exact hmono.trans_eq h42
    omega
  rcases le_or_gt k.val 46 with hk46 | hk47
  · have hpi : Nat.primeCounting k.val ≤ 14 := by
      have hmono := Nat.monotone_primeCounting hk46
      have h46 : Nat.primeCounting 46 = 14 := by decide
      exact hmono.trans_eq h46
    omega
  rcases le_or_gt k.val 52 with hk52 | hk53
  · have hpi : Nat.primeCounting k.val ≤ 15 := by
      have hmono := Nat.monotone_primeCounting hk52
      have h52 : Nat.primeCounting 52 = 15 := by decide
      exact hmono.trans_eq h52
    omega
  rcases le_or_gt k.val 60 with hk60 | hk61
  · have hpi : Nat.primeCounting k.val ≤ 17 := by
      have hmono := Nat.monotone_primeCounting hk60
      have h60 : Nat.primeCounting 60 = 17 := by decide
      exact hmono.trans_eq h60
    omega
  rcases le_or_gt k.val 72 with hk72 | hk73
  · have hpi : Nat.primeCounting k.val ≤ 20 := by
      have hmono := Nat.monotone_primeCounting hk72
      have h72 : Nat.primeCounting 72 = 20 := by decide
      exact hmono.trans_eq h72
    omega
  rcases le_or_gt k.val 96 with hk96 | hk97
  · have hpi : Nat.primeCounting k.val ≤ 24 := by
      have hmono := Nat.monotone_primeCounting hk96
      have h96 : Nat.primeCounting 96 = 24 := by
        set_option maxRecDepth 10000 in
        decide
      exact hmono.trans_eq h96
    omega
  rcases le_or_gt k.val 136 with hk136 | hk137
  · have hpi : Nat.primeCounting k.val ≤ 32 := by
      have hmono := Nat.monotone_primeCounting hk136
      have h136 : Nat.primeCounting 136 = 32 := by
        set_option maxRecDepth 10000 in
        decide
      exact hmono.trans_eq h136
    omega
  · have hpi : Nat.primeCounting k.val ≤ 35 := by
      have hmono := Nat.monotone_primeCounting k.isLt.le
      have h149 : Nat.primeCounting 149 = 35 := by
        set_option maxRecDepth 10000 in
        decide
      set_option maxRecDepth 10000 in
      exact hmono.trans_eq h149
    omega

theorem three_mul_primeCounting_le_of_33_le {k : ℕ} (hk33 : 33 ≤ k) :
    3 * Nat.primeCounting k ≤ k := by
  by_cases hk150 : k < 150
  · exact three_mul_primeCounting_le_30_150_cert ⟨k, hk150⟩ hk33
  · let m := k - 30
    have hk_eq : k = 30 + m := by omega
    have hbound0 := Nat.primeCounting_add_le
      (a := 30) (k := 30) (n := m) (by norm_num) (by norm_num : 30 ≤ 30)
    have hbound : Nat.primeCounting k ≤ Nat.primeCounting 30 + Nat.totient 30 * (m / 30 + 1) := by
      simpa [hk_eq] using hbound0
    have hcalc : Nat.primeCounting 30 = 10 := by decide
    have htot : Nat.totient 30 = 8 := by decide
    have hbound2 : Nat.primeCounting k ≤ 10 + 8 * (m / 30 + 1) := by
      simpa [hcalc, htot] using hbound
    have hm120 : 120 ≤ m := by omega
    have hq4 : 4 ≤ m / 30 := by
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 30)).mpr hm120
    have hmul : 30 * (m / 30) ≤ m := Nat.mul_div_le m 30
    omega

theorem log_choose_le_sqrt_third_log_add_min_third_log_two_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrt33 : 33 ≤ sqrt n)
    (hsqrtM : sqrt n ≤ min k (n / 3)) (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    Real.log (n.choose k) ≤
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 := by
  have hupper :=
    log_choose_le_primeCounting_sqrt_log_add_min_third_log_two_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrtM hMsub
  have hlogn_pos : 0 < Real.log n := by
    have hn_gt_one : 1 < n := lt_of_lt_of_le (by omega : 1 < sqrt n) (Nat.sqrt_le_self n)
    exact Real.log_pos (by exact_mod_cast hn_gt_one)
  have hpi : 3 * Nat.primeCounting (sqrt n) ≤ sqrt n :=
    three_mul_primeCounting_le_of_33_le hsqrt33
  have hpi_real : (Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) / 3 := by
    nlinarith [show (3 * Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) by
      exact_mod_cast hpi]
  exact hupper.trans <|
    add_le_add_left (mul_le_mul_of_nonneg_right hpi_real hlogn_pos.le)
      (((min k (n / 3) : ℕ) : ℝ) * Real.log 2)

theorem log_choose_le_sqrt_third_log_add_min_log4_sub_theta_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrt33 : 33 ≤ sqrt n)
    (hsqrtM : sqrt n ≤ min k (n / 3)) :
    Real.log (n.choose k) ≤
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4
        - Chebyshev.theta ((sqrt n : ℕ) : ℝ) := by
  have hupper :=
    log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno
  have hlogP :=
    log_primeIntervalProduct_le_min_third_log4_sub_theta
      (a := sqrt n) (M := min k (n / 3)) hsqrtM
  have hlogn_pos : 0 < Real.log n := by
    have hn_gt_one : 1 < n := lt_of_lt_of_le (by omega : 1 < sqrt n) (Nat.sqrt_le_self n)
    exact Real.log_pos (by exact_mod_cast hn_gt_one)
  have hpi : 3 * Nat.primeCounting (sqrt n) ≤ sqrt n :=
    three_mul_primeCounting_le_of_33_le hsqrt33
  have hpi_real : (Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) / 3 := by
    nlinarith [show (3 * Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) by
      exact_mod_cast hpi]
  have hpc :
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n ≤
        ((sqrt n : ℕ) : ℝ) / 3 * Real.log n :=
    mul_le_mul_of_nonneg_right hpi_real hlogn_pos.le
  linarith

theorem exists_large_prime_factor_choose_of_theta_interval_entropy_gap
    {n k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hsqrt33 : 33 ≤ sqrt n) (hsqrtM : sqrt n ≤ min k (n / 3))
    (hgap :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4
          - Chebyshev.theta ((sqrt n : ℕ) : ℝ) <
        entropyTerm n k
          + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
          + Real.log (2 * Real.pi) / 2 - 2) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < n := hkpos.trans hklt
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hupper :=
    log_choose_le_sqrt_third_log_add_min_log4_sub_theta_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrt33 hsqrtM
  have hlower := entropy_lower_le_log_choose (n := n) (k := k) hkpos hklt
  exact not_lt_of_ge (hlower.trans hupper) hgap

theorem min_eq_left_of_sqrt33_close
    {n k : ℕ} (hsqrt33 : 33 ≤ sqrt n)
    (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    min k (n / 3) = k := by
  by_cases hk : k ≤ n / 3
  · exact Nat.min_eq_left hk
  · have hM : min k (n / 3) = n / 3 := Nat.min_eq_right (le_of_not_ge hk)
    have hclose : n / 3 ≤ 2 * sqrt n := by
      omega
    have hnle : n ≤ 3 * (n / 3) + 2 := by omega
    have hsq : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
    nlinarith

theorem close_branch_coef_gap_aux {L N : ℝ} (h10 : 10 * L < N) (hL : L < 1) :
    (2 : ℝ) / 3 < N / 6 - 2 * L + 1 := by
  linarith

theorem close_branch_main_gap_aux {k N L : ℝ} (hk : 34 ≤ k) (hN : N / 2 ≤ k / 6)
    (hc : (2 : ℝ) / 3 < N / 6 - 2 * L + 1) :
    0 < k * (N / 6 - 2 * L + 1) - N / 2 - 6 := by
  have hkpos : 0 < k := by linarith
  have hprod :
      k * ((2 : ℝ) / 3) < k * (N / 6 - 2 * L + 1) :=
    mul_lt_mul_of_pos_left hc hkpos
  nlinarith

theorem close_branch_simple_gap_aux {k N L : ℝ}
    (h : 0 < k * (N / 6 - 2 * L + 1) - N / 2 - 6) :
    k / 3 * N + k * L <
      (k / 2 * N - k * L + k - 4) - N / 2 - 2 := by
  nlinarith

theorem close_branch_shift_aux {A B N : ℝ} (h : A ≤ B) :
    A - N / 2 - 2 ≤ B - N / 2 - 2 := by
  linarith

theorem close_branch_upper_simple_aux {a k M : ℕ} {N L : ℝ}
    (hM : M = k) (ha : a ≤ k) (hN : 0 ≤ N) :
    (a : ℝ) / 3 * N + (M : ℝ) * L ≤ (k : ℝ) / 3 * N + (k : ℝ) * L := by
  subst M
  have ha_real : (a : ℝ) / 3 ≤ (k : ℝ) / 3 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha) (by norm_num)
  exact add_le_add_left (mul_le_mul_of_nonneg_right ha_real hN) ((k : ℝ) * L)

theorem log2_lt_7_10 : Real.log 2 < (7 : ℝ) / 10 := by
  nlinarith [Real.log_two_lt_d9]

theorem log4_lt_7_5 : Real.log 4 < (7 : ℝ) / 5 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  nlinarith [log2_lt_7_10]

theorem log2_lt_1733_2500 : Real.log 2 < (1733 : ℝ) / 2500 := by
  nlinarith [Real.log_two_lt_d9]

theorem log4_lt_1733_1250 : Real.log 4 < (1733 : ℝ) / 1250 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  nlinarith [log2_lt_1733_2500]

theorem log4_gt_69_50 : (69 : ℝ) / 50 < Real.log 4 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  nlinarith [Real.log_two_gt_d9]

theorem log16_gt_69_25 : (69 : ℝ) / 25 < Real.log 16 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  nlinarith [Real.log_two_gt_d9]

theorem log64_lt_21_5 : Real.log 64 < (21 : ℝ) / 5 := by
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
  nlinarith [log2_lt_7_10]

theorem log_le_div64_add_16_5_of_120_le {k : ℕ} (hk120 : 120 ≤ k) :
    Real.log k ≤ (k : ℝ) / 64 + (16 : ℝ) / 5 := by
  have hkpos : 0 < k := by omega
  have hdivpos : 0 < (k : ℝ) / 64 := by positivity
  have hlogdiv := Real.log_le_sub_one_of_pos (x := (k : ℝ) / 64) hdivpos
  rw [Real.log_div (by exact_mod_cast hkpos.ne' : (k : ℝ) ≠ 0)
    (by norm_num : (64 : ℝ) ≠ 0)] at hlogdiv
  nlinarith [log64_lt_21_5]

theorem large_k_stirling_tail_lt_div32 {k : ℕ} (hk120 : 120 ≤ k) :
    Real.log k / 2 + (6 : ℝ) / 5 < (k : ℝ) / 32 := by
  have hlog := log_le_div64_add_16_5_of_120_le hk120
  have hkreal : (120 : ℝ) ≤ k := by exact_mod_cast hk120
  nlinarith

theorem log6_gt_8_5 : (8 : ℝ) / 5 < Real.log 6 := by
  have hlog2 : (69 : ℝ) / 100 < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr Real.exp_one_lt_three
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul]
    all_goals norm_num
  nlinarith

theorem stirling_correction_ge_neg_log_k_sub_six_fifths
    {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    - Real.log k / 2 - (6 : ℝ) / 5 ≤
      Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
        + Real.log (2 * Real.pi) / 2 - 2 := by
  have hnkpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) :=
    Nat.cast_sub (le_of_lt hklt)
  have hnkpos_real : (0 : ℝ) < (n : ℝ) - (k : ℝ) := by
    rw [← hcast_sub]
    exact_mod_cast hnkpos
  have hnk_le_n_real : (n : ℝ) - (k : ℝ) ≤ (n : ℝ) := by
    have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    linarith
  have hlognk_le_logn : Real.log (n - k) ≤ Real.log n :=
    Real.log_le_log hnkpos_real hnk_le_n_real
  have htwopi : (6 : ℝ) < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hlog6_le : Real.log 6 ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log (by norm_num) htwopi.le
  nlinarith [log6_gt_8_5, hlog6_le]

theorem entropyTerm_eq_mul_entropyRatio
    {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    entropyTerm n k =
      (k : ℝ) * (((n : ℝ) / (k : ℝ)) * Real.log ((n : ℝ) / (k : ℝ))
        - ((n : ℝ) / (k : ℝ) - 1) * Real.log ((n : ℝ) / (k : ℝ) - 1)) := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < n := hkpos.trans hklt
  have hnkpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hkpos_real : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hnpos_real : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnkpos_real_nat : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast hnkpos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hkpos_real
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnpos_real
  have hnk_ne : ((n - k : ℕ) : ℝ) ≠ 0 := ne_of_gt hnkpos_real_nat
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hkn
  have hratio_sub :
      (n : ℝ) / (k : ℝ) - 1 = ((n - k : ℕ) : ℝ) / (k : ℝ) := by
    rw [hcast_sub]
    field_simp [hk_ne]
  unfold entropyTerm
  rw [Real.log_div hn_ne hk_ne, hratio_sub, Real.log_div hnk_ne hk_ne]
  rw [hcast_sub]
  field_simp [hk_ne]
  ring

theorem entropyRatio_lower_log_add
    {x : ℝ} (hx : 1 < x) :
    Real.log x + 1 - 1 / x ≤
      x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hxpos : 0 < x := by linarith
  have hxsubpos : 0 < x - 1 := by linarith
  have hypos : 0 < x / (x - 1) := div_pos hxpos hxsubpos
  have hlog := Real.one_sub_inv_le_log_of_pos hypos
  have hrewrite :
      Real.log x + (x - 1) * Real.log (x / (x - 1)) =
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hxsubpos)]
    ring
  have hinv_eq : (x / (x - 1))⁻¹ = (x - 1) / x := by
    field_simp [ne_of_gt hxpos, ne_of_gt hxsubpos]
  rw [hinv_eq] at hlog
  have hlog' : 1 / x ≤ Real.log (x / (x - 1)) := by
    field_simp [ne_of_gt hxpos] at hlog ⊢
    linarith
  have hmul :
      (x - 1) * (1 / x) ≤ (x - 1) * Real.log (x / (x - 1)) :=
    mul_le_mul_of_nonneg_left hlog' (by linarith)
  have hbasic :
      Real.log x + 1 - 1 / x ≤
        Real.log x + (x - 1) * Real.log (x / (x - 1)) := by
    field_simp [ne_of_gt hxpos, ne_of_gt hxsubpos] at hmul ⊢
    nlinarith
  rwa [hrewrite] at hbasic

theorem two_mul_sub_one_div_add_one_le_log {x : ℝ} (hx1 : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  by_cases hx : x = 1
  · subst x
    norm_num
  have hxgt : 1 < x := lt_of_le_of_ne hx1 (Ne.symm hx)
  let u : ℝ := (x - 1) / (x + 1)
  have hdenpos : 0 < x + 1 := by linarith
  have hu0 : 0 ≤ u := by
    exact div_nonneg (by linarith) hdenpos.le
  have hu1 : u < 1 := by
    rw [show u = (x - 1) / (x + 1) by rfl]
    rw [div_lt_one hdenpos]
    linarith
  have hsum := Real.sum_range_le_log_div hu0 hu1 1
  norm_num at hsum
  have hratio : (1 + u) / (1 - u) = x := by
    rw [show u = (x - 1) / (x + 1) by rfl]
    field_simp [hdenpos.ne']
    ring
  rw [hratio] at hsum
  have hleft : 2 * (x - 1) / (x + 1) = 2 * u := by
    rw [show u = (x - 1) / (x + 1) by rfl]
    ring
  rw [hleft]
  nlinarith

theorem two_div_two_mul_sub_one_le_log_div_sub_one {x : ℝ} (hx : 1 < x) :
    2 / (2 * x - 1) ≤ Real.log (x / (x - 1)) := by
  have hy1 : 1 ≤ x / (x - 1) := by
    have hden : 0 < x - 1 := by linarith
    rw [one_le_div hden]
    linarith
  have h := two_mul_sub_one_div_add_one_le_log hy1
  have hden : 0 < x - 1 := by linarith
  have hden2 : 0 < 2 * x - 1 := by linarith
  convert h using 1
  field_simp [hden.ne', hden2.ne']
  ring

theorem entropyRatio_lower_log_add_two_div
    {x : ℝ} (hx : 1 < x) :
    Real.log x + (x - 1) * (2 / (2 * x - 1)) ≤
      x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hxpos : 0 < x := by linarith
  have hxsubpos : 0 < x - 1 := by linarith
  have hratio := two_div_two_mul_sub_one_le_log_div_sub_one hx
  have hmul :
      (x - 1) * (2 / (2 * x - 1)) ≤
        (x - 1) * Real.log (x / (x - 1)) :=
    mul_le_mul_of_nonneg_left hratio (by linarith)
  have hrewrite :
      Real.log x + (x - 1) * Real.log (x / (x - 1)) =
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hxsubpos)]
    ring
  linarith

theorem sqrt_div_mul_log_mul_le_of_120_le
    {K x : ℝ} (hK : 120 ≤ K) (hx : 2 ≤ x) :
    Real.sqrt (x / K) * Real.log (K * x) ≤
      Real.sqrt (x / 120) * Real.log (120 * x) := by
  have hxpos : 0 < x := by linarith
  have hKpos : 0 < K := by linarith
  have h120pos : (0 : ℝ) < 120 := by norm_num
  have hz0 : Real.exp 2 ≤ 120 * x := by
    have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hexp1pos : 0 < Real.exp 1 := Real.exp_pos 1
    have hexp2 : Real.exp 2 < 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    nlinarith
  have hzK : Real.exp 2 ≤ K * x := by
    have hle : 120 * x ≤ K * x := mul_le_mul_of_nonneg_right hK hxpos.le
    exact hz0.trans hle
  have hKx : 120 * x ≤ K * x := mul_le_mul_of_nonneg_right hK hxpos.le
  have hanti := Real.log_div_sqrt_antitoneOn hz0 hzK hKx
  have hscale :
      x * (Real.log (K * x) / Real.sqrt (K * x)) ≤
        x * (Real.log (120 * x) / Real.sqrt (120 * x)) :=
    mul_le_mul_of_nonneg_left hanti hxpos.le
  have hleft :
      Real.sqrt (x / K) * Real.log (K * x) =
        x * (Real.log (K * x) / Real.sqrt (K * x)) := by
    rw [Real.sqrt_div hxpos.le, Real.sqrt_mul hKpos.le]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hxpos), ne_of_gt (Real.sqrt_pos_of_pos hKpos)]
    rw [Real.sq_sqrt hxpos.le]
  have hright :
      Real.sqrt (x / 120) * Real.log (120 * x) =
        x * (Real.log (120 * x) / Real.sqrt (120 * x)) := by
    rw [Real.sqrt_div hxpos.le, Real.sqrt_mul h120pos.le]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hxpos), ne_of_gt (Real.sqrt_pos_of_pos h120pos)]
    rw [Real.sq_sqrt hxpos.le]
  rw [hleft, hright]
  exact hscale

theorem sqrt_div_mul_log_mul_le_of_base_le
    {K0 K x : ℝ} (hK0pos : 0 < K0) (hK0K : K0 ≤ K) (hxpos : 0 < x)
    (hexp : Real.exp 2 ≤ K0 * x) :
    Real.sqrt (x / K) * Real.log (K * x) ≤
      Real.sqrt (x / K0) * Real.log (K0 * x) := by
  have hKpos : 0 < K := hK0pos.trans_le hK0K
  have hzK : Real.exp 2 ≤ K * x := by
    have hle : K0 * x ≤ K * x := mul_le_mul_of_nonneg_right hK0K hxpos.le
    exact hexp.trans hle
  have hKx : K0 * x ≤ K * x := mul_le_mul_of_nonneg_right hK0K hxpos.le
  have hanti := Real.log_div_sqrt_antitoneOn hexp hzK hKx
  have hscale :
      x * (Real.log (K * x) / Real.sqrt (K * x)) ≤
        x * (Real.log (K0 * x) / Real.sqrt (K0 * x)) :=
    mul_le_mul_of_nonneg_left hanti hxpos.le
  have hleft :
      Real.sqrt (x / K) * Real.log (K * x) =
        x * (Real.log (K * x) / Real.sqrt (K * x)) := by
    rw [Real.sqrt_div hxpos.le, Real.sqrt_mul hKpos.le]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hxpos), ne_of_gt (Real.sqrt_pos_of_pos hKpos)]
    rw [Real.sq_sqrt hxpos.le]
  have hright :
      Real.sqrt (x / K0) * Real.log (K0 * x) =
        x * (Real.log (K0 * x) / Real.sqrt (K0 * x)) := by
    rw [Real.sqrt_div hxpos.le, Real.sqrt_mul hK0pos.le]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hxpos), ne_of_gt (Real.sqrt_pos_of_pos hK0pos)]
    rw [Real.sq_sqrt hxpos.le]
  rw [hleft, hright]
  exact hscale

theorem nat_sqrt_div_le_sqrt_ratio {n k : ℕ} (hkpos : 0 < k) :
    ((sqrt n : ℕ) : ℝ) / (k : ℝ) ≤
      Real.sqrt (((n : ℝ) / (k : ℝ)) / (k : ℝ)) := by
  have hkpos_real : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hnonneg : 0 ≤ ((sqrt n : ℕ) : ℝ) / (k : ℝ) := by positivity
  have harg_nonneg : 0 ≤ ((n : ℝ) / (k : ℝ)) / (k : ℝ) := by positivity
  have hsqrt_sq_nat : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
  have hsqrt_sq_real : (((sqrt n : ℕ) : ℝ) / (k : ℝ)) ^ 2 ≤
      ((n : ℝ) / (k : ℝ)) / (k : ℝ) := by
    have hcast : (((sqrt n : ℕ) : ℝ) ^ 2) ≤ (n : ℝ) := by
      norm_num [pow_two]
      exact_mod_cast hsqrt_sq_nat
    field_simp [ne_of_gt hkpos_real]
    nlinarith
  exact (Real.le_sqrt hnonneg harg_nonneg).mpr hsqrt_sq_real

theorem log360_lt_6 : Real.log 360 < (6 : ℝ) := by
  have hfracpos : (0 : ℝ) < 360 / 256 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (360 : ℝ) / 256) hfracpos
  rw [Real.log_div (by norm_num : (360 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0)] at hfrac
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  rw [h256] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log420_lt_31_5 : Real.log 420 < (31 : ℝ) / 5 := by
  have hfracpos : (0 : ℝ) < 420 / 256 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (420 : ℝ) / 256) hfracpos
  rw [Real.log_div (by norm_num : (420 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0)] at hfrac
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  rw [h256] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log480_lt_13_2 : Real.log 480 < (13 : ℝ) / 2 := by
  have hfracpos : (0 : ℝ) < 480 / 256 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (480 : ℝ) / 256) hfracpos
  rw [Real.log_div (by norm_num : (480 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0)] at hfrac
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  rw [h256] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log720_lt_20_3 : Real.log 720 < (20 : ℝ) / 3 := by
  have hfracpos : (0 : ℝ) < 720 / 512 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (720 : ℝ) / 512) hfracpos
  rw [Real.log_div (by norm_num : (720 : ℝ) ≠ 0) (by norm_num : (512 : ℝ) ≠ 0)] at hfrac
  have h512 : Real.log 512 = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
    norm_num
  rw [h512] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log1200_lt_15_2 : Real.log 1200 < (15 : ℝ) / 2 := by
  have hfracpos : (0 : ℝ) < 1200 / 1024 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (1200 : ℝ) / 1024) hfracpos
  rw [Real.log_div (by norm_num : (1200 : ℝ) ≠ 0) (by norm_num : (1024 : ℝ) ≠ 0)] at hfrac
  have h1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [h1024] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log1920_lt_8 : Real.log 1920 < (8 : ℝ) := by
  have hfracpos : (0 : ℝ) < 1920 / 1024 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (1920 : ℝ) / 1024) hfracpos
  rw [Real.log_div (by norm_num : (1920 : ℝ) ≠ 0) (by norm_num : (1024 : ℝ) ≠ 0)] at hfrac
  have h1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [h1024] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log2880_lt_41_5 : Real.log 2880 < (41 : ℝ) / 5 := by
  have hfracpos : (0 : ℝ) < 2880 / 2048 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (2880 : ℝ) / 2048) hfracpos
  rw [Real.log_div (by norm_num : (2880 : ℝ) ≠ 0) (by norm_num : (2048 : ℝ) ≠ 0)] at hfrac
  have h2048 : Real.log 2048 = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
    norm_num
  rw [h2048] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem log3720_lt_43_5 : Real.log 3720 < (43 : ℝ) / 5 := by
  have hfracpos : (0 : ℝ) < 3720 / 2048 := by norm_num
  have hfrac := Real.log_le_sub_one_of_pos (x := (3720 : ℝ) / 2048) hfracpos
  rw [Real.log_div (by norm_num : (3720 : ℝ) ≠ 0) (by norm_num : (2048 : ℝ) ≠ 0)] at hfrac
  have h2048 : Real.log 2048 = 11 * Real.log 2 := by
    rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
    norm_num
  rw [h2048] at hfrac
  nlinarith [log2_lt_1733_2500]

theorem sqrt_log120_mul_le_1_3_of_2_le_of_le_3 {x : ℝ} (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (1 : ℝ) / 3 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (1 : ℝ) / 6 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (6 : ℝ) := by
    have hle : 120 * x ≤ (360 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log360_lt_6.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_3_8_of_3_le_of_le_7_2 {x : ℝ}
    (hx3 : 3 ≤ x) (hx7 : x ≤ (7 : ℝ) / 2) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (3 : ℝ) / 8 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (7 : ℝ) / 40 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 7 / 40)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (31 : ℝ) / 5 := by
    have hle : 120 * x ≤ (420 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log420_lt_31_5.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_2_5_of_7_2_le_of_le_4 {x : ℝ}
    (hx7 : (7 : ℝ) / 2 ≤ x) (hx4 : x ≤ 4) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (2 : ℝ) / 5 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (11 : ℝ) / 60 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (11 : ℝ) / 60)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (13 : ℝ) / 2 := by
    have hle : 120 * x ≤ (480 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log480_lt_13_2.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_1_2_of_4_le_of_le_6 {x : ℝ} (hx4 : 4 ≤ x) (hx6 : x ≤ 6) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (1 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (9 : ℝ) / 40 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (9 : ℝ) / 40)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (20 : ℝ) / 3 := by
    have hle : 120 * x ≤ (720 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log720_lt_20_3.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_3_4_of_6_le_of_le_10 {x : ℝ} (hx6 : 6 ≤ x) (hx10 : x ≤ 10) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (3 : ℝ) / 4 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (3 : ℝ) / 10 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 10)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (15 : ℝ) / 2 := by
    have hle : 120 * x ≤ (1200 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log1200_lt_15_2.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_1_of_10_le_of_le_16 {x : ℝ} (hx10 : 10 ≤ x) (hx16 : x ≤ 16) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (1 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (3 : ℝ) / 8 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 8)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (8 : ℝ) := by
    have hle : 120 * x ≤ (1920 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log1920_lt_8.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_5_4_of_16_le_of_le_24 {x : ℝ} (hx16 : 16 ≤ x) (hx24 : x ≤ 24) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (5 : ℝ) / 4 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (9 : ℝ) / 20 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (9 : ℝ) / 20)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (41 : ℝ) / 5 := by
    have hle : 120 * x ≤ (2880 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log2880_lt_41_5.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem sqrt_log120_mul_le_3_2_of_24_le_of_le_31 {x : ℝ} (hx24 : 24 ≤ x) (hx31 : x ≤ 31) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x) ≤ (3 : ℝ) / 2 := by
  have hxpos : 0 < x := by linarith
  have hsqrt : Real.sqrt (x / 120) ≤ (13 : ℝ) / 25 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (13 : ℝ) / 25)]
    nlinarith
  have hlog : Real.log (120 * x) ≤ (43 : ℝ) / 5 := by
    have hle : 120 * x ≤ (3720 : ℝ) := by nlinarith
    exact (Real.log_le_log (by nlinarith : (0 : ℝ) < 120 * x) hle).trans log3720_lt_43_5.le
  have hlog_nonneg : 0 ≤ Real.log (120 * x) := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 120 * x)
  have hmul := mul_le_mul hsqrt hlog hlog_nonneg (by norm_num)
  nlinarith

theorem far_core_aux_2_3 {x : ℝ} (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    (1 : ℝ) / 32 + x / 3 * ((1733 : ℝ) / 1250) + (1 : ℝ) / 3 ≤
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) := by
  have hden1 : 0 < x + 1 := by linarith
  have hden2 : 0 < 2 * x - 1 := by linarith
  have ht0 : 0 ≤ x - 2 := by linarith
  have ht1 : 0 ≤ 3 - x := by linarith
  have hp :
      0 ≤ -55456 * x ^ 3 + 288522 * x ^ 2 - 354147 * x + (21875 : ℝ) := by
    have h0 : 0 ≤ (24021 : ℝ) * (3 - x) ^ 3 := by positivity
    have h1 : 0 ≤ (3 : ℝ) * 68844 * (x - 2) * (3 - x) ^ 2 := by positivity
    have h2 : 0 ≤ (3 : ℝ) * 98929 * (x - 2) ^ 2 * (3 - x) := by positivity
    have h3 : 0 ≤ (58820 : ℝ) * (x - 2) ^ 3 := by positivity
    have hid :
        -55456 * x ^ 3 + 288522 * x ^ 2 - 354147 * x + (21875 : ℝ) =
          24021 * (3 - x) ^ 3 + 3 * 68844 * (x - 2) * (3 - x) ^ 2
            + 3 * 98929 * (x - 2) ^ 2 * (3 - x) + 58820 * (x - 2) ^ 3 := by
      ring
    rw [hid]
    positivity
  have hdenpos : 0 < (60000 : ℝ) * (x + 1) * (2 * x - 1) := by positivity
  have hfrac :
      0 ≤ (-55456 * x ^ 3 + 288522 * x ^ 2 - 354147 * x + (21875 : ℝ)) /
        ((60000 : ℝ) * (x + 1) * (2 * x - 1)) :=
    div_nonneg hp hdenpos.le
  have hdiff :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1))
        - ((1 : ℝ) / 32 + x / 3 * ((1733 : ℝ) / 1250) + (1 : ℝ) / 3)
      =
      (-55456 * x ^ 3 + 288522 * x ^ 2 - 354147 * x + (21875 : ℝ)) /
        ((60000 : ℝ) * (x + 1) * (2 * x - 1)) := by
    field_simp [hden1.ne', hden2.ne']
    ring
  linarith

theorem far_core_aux_3_7_2 {x : ℝ} (hx3 : 3 ≤ x) (_hx7 : x ≤ (7 : ℝ) / 2) :
    (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (3 : ℝ) / 8 ≤
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) := by
  have hden1 : 0 < x + 1 := by linarith
  have hden2 : 0 < 2 * x - 1 := by linarith
  have ht : 0 ≤ x - 3 := by linarith
  have hp : 0 ≤ (16098 : ℝ) * x ^ 2 - 51951 * x + 11951 := by
    have hid : (16098 : ℝ) * x ^ 2 - 51951 * x + 11951 =
        16098 * (x - 3) ^ 2 + 44637 * (x - 3) + 980 := by ring
    rw [hid]
    positivity
  have hdenpos : 0 < (20000 : ℝ) * (x + 1) * (2 * x - 1) := by positivity
  have hfrac :
      0 ≤ (3 * ((16098 : ℝ) * x ^ 2 - 51951 * x + 11951)) /
        ((20000 : ℝ) * (x + 1) * (2 * x - 1)) :=
    div_nonneg (by positivity) hdenpos.le
  have hdiff :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1))
        - ((1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (3 : ℝ) / 8)
      =
      (3 * ((16098 : ℝ) * x ^ 2 - 51951 * x + 11951)) /
        ((20000 : ℝ) * (x + 1) * (2 * x - 1)) := by
    field_simp [hden1.ne', hden2.ne']
    ring
  linarith

theorem far_core_aux_7_2_4 {x : ℝ} (hx7 : (7 : ℝ) / 2 ≤ x) (_hx4 : x ≤ 4) :
    (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (2 : ℝ) / 5 ≤
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) := by
  have hden1 : 0 < x + 1 := by linarith
  have hden2 : 0 < 2 * x - 1 := by linarith
  have ht : 0 ≤ x - (7 : ℝ) / 2 := by linarith
  have hp : 0 ≤ (47294 : ℝ) * x ^ 2 - 156353 * x + 36353 := by
    have hid : (47294 : ℝ) * x ^ 2 - 156353 * x + 36353 =
        47294 * (x - (7 : ℝ) / 2) ^ 2 + 174705 * (x - (7 : ℝ) / 2) + 68469 := by
      ring
    rw [hid]
    positivity
  have hdenpos : 0 < (20000 : ℝ) * (x + 1) * (2 * x - 1) := by positivity
  have hfrac :
      0 ≤ ((47294 : ℝ) * x ^ 2 - 156353 * x + 36353) /
        ((20000 : ℝ) * (x + 1) * (2 * x - 1)) :=
    div_nonneg hp hdenpos.le
  have hdiff :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1))
        - ((1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (2 : ℝ) / 5)
      =
      ((47294 : ℝ) * x ^ 2 - 156353 * x + 36353) /
        ((20000 : ℝ) * (x + 1) * (2 * x - 1)) := by
    field_simp [hden1.ne', hden2.ne']
    ring
  linarith

theorem below_square_B_core_2_3 {x : ℝ} (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_1_3_of_2_le_of_le_3 hx2 hx3
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog :
      min 1 (x / 3) * Real.log 4 ≤ x / 3 * ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ (x / 3) * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_right 1 (x / 3)) hlog4_nonneg
      _ ≤ (x / 3) * ((1733 : ℝ) / 1250) := by
        exact mul_le_mul_of_nonneg_left log4_lt_1733_1250.le (by nlinarith)
  have haux := far_core_aux_2_3 hx2 hx3
  have hlogx := two_mul_sub_one_div_add_one_le_log (by linarith : (1 : ℝ) ≤ x)
  have hlower := entropyRatio_lower_log_add_two_div hx1
  have hrat_lower :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) ≤
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    linarith
  linarith

theorem below_square_B_core_3_7_2 {x : ℝ} (hx3 : 3 ≤ x) (hx7 : x ≤ (7 : ℝ) / 2) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_3_8_of_3_le_of_le_7_2 hx3 hx7
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog :
      min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by
        nlinarith [log4_lt_1733_1250]
  have haux := far_core_aux_3_7_2 hx3 hx7
  have hlogx := two_mul_sub_one_div_add_one_le_log (by linarith : (1 : ℝ) ≤ x)
  have hlower := entropyRatio_lower_log_add_two_div hx1
  have hrat_lower :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) ≤
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    linarith
  linarith

theorem below_square_B_core_7_2_4 {x : ℝ} (hx7 : (7 : ℝ) / 2 ≤ x) (hx4 : x ≤ 4) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_2_5_of_7_2_le_of_le_4 hx7 hx4
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog :
      min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by
        nlinarith [log4_lt_1733_1250]
  have haux := far_core_aux_7_2_4 hx7 hx4
  have hlogx := two_mul_sub_one_div_add_one_le_log (by linarith : (1 : ℝ) ≤ x)
  have hlower := entropyRatio_lower_log_add_two_div hx1
  have hrat_lower :
      2 * (x - 1) / (x + 1) + (x - 1) * (2 / (2 * x - 1)) ≤
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    linarith
  linarith

theorem below_square_B_core_4_6 {x : ℝ} (hx4 : 4 ≤ x) (hx6 : x ≤ 6) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_1_2_of_4_le_of_le_6 hx4 hx6
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by nlinarith [log4_lt_1733_1250]
  have hlogx : (69 : ℝ) / 50 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx4
    nlinarith [hlelog, log4_gt_69_50]
  have haux : (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (1 : ℝ) / 2
      ≤ (69 : ℝ) / 50 + 1 - 1 / x := by
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x ≤ (1 : ℝ) / 4 := by
      exact one_div_le_one_div_of_le (by norm_num) hx4
    nlinarith
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core_6_10 {x : ℝ} (hx6 : 6 ≤ x) (hx10 : x ≤ 10) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_3_4_of_6_le_of_le_10 hx6 hx10
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by nlinarith [log4_lt_1733_1250]
  have hlogx : (8 : ℝ) / 5 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 6) hx6
    nlinarith [hlelog, log6_gt_8_5]
  have haux : (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (3 : ℝ) / 4
      ≤ (8 : ℝ) / 5 + 1 - 1 / x := by
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x ≤ (1 : ℝ) / 6 := by
      exact one_div_le_one_div_of_le (by norm_num) hx6
    nlinarith
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core_10_16 {x : ℝ} (hx10 : 10 ≤ x) (hx16 : x ≤ 16) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_1_of_10_le_of_le_16 hx10 hx16
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by nlinarith [log4_lt_1733_1250]
  have hlogx : (8 : ℝ) / 5 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 6) (by linarith : (6 : ℝ) ≤ x)
    nlinarith [hlelog, log6_gt_8_5]
  have haux : (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (1 : ℝ)
      ≤ (8 : ℝ) / 5 + 1 - 1 / x := by
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x ≤ (1 : ℝ) / 10 := by
      exact one_div_le_one_div_of_le (by norm_num) hx10
    nlinarith
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core_16_24 {x : ℝ} (hx16 : 16 ≤ x) (hx24 : x ≤ 24) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_5_4_of_16_le_of_le_24 hx16 hx24
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by nlinarith [log4_lt_1733_1250]
  have hlogx : (69 : ℝ) / 25 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hx16
    nlinarith [hlelog, log16_gt_69_25]
  have haux : (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (5 : ℝ) / 4
      ≤ (69 : ℝ) / 25 + 1 - 1 / x := by
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x ≤ (1 : ℝ) / 16 := by
      exact one_div_le_one_div_of_le (by norm_num) hx16
    nlinarith
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core_24_31 {x : ℝ} (hx24 : 24 ≤ x) (hx31 : x ≤ 31) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hx1 : 1 < x := by linarith
  have hterm := sqrt_log120_mul_le_3_2_of_24_le_of_le_31 hx24 hx31
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ ((1733 : ℝ) / 1250) := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ ((1733 : ℝ) / 1250) := by nlinarith [log4_lt_1733_1250]
  have hlogx : (69 : ℝ) / 25 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by linarith : (16 : ℝ) ≤ x)
    nlinarith [hlelog, log16_gt_69_25]
  have haux : (1 : ℝ) / 32 + ((1733 : ℝ) / 1250) + (3 : ℝ) / 2
      ≤ (69 : ℝ) / 25 + 1 - 1 / x := by
    have hxpos : 0 < x := by linarith
    have hinv : 1 / x ≤ (1 : ℝ) / 24 := by
      exact one_div_le_one_div_of_le (by norm_num) hx24
    nlinarith
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core_compact {x : ℝ} (hx2 : 2 ≤ x) (hx31 : x ≤ 31) :
    Real.sqrt (x / 120) / 3 * Real.log (120 * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  by_cases hx3 : x ≤ 3
  · exact below_square_B_core_2_3 hx2 hx3
  · have hx3' : 3 ≤ x := by linarith
    by_cases hx7 : x ≤ (7 : ℝ) / 2
    · exact below_square_B_core_3_7_2 hx3' hx7
    · have hx7' : (7 : ℝ) / 2 ≤ x := by linarith
      by_cases hx4 : x ≤ 4
      · exact below_square_B_core_7_2_4 hx7' hx4
      · have hx4' : 4 ≤ x := by linarith
        by_cases hx6 : x ≤ 6
        · exact below_square_B_core_4_6 hx4' hx6
        · have hx6' : 6 ≤ x := by linarith
          by_cases hx10 : x ≤ 10
          · exact below_square_B_core_6_10 hx6' hx10
          · have hx10' : 10 ≤ x := by linarith
            by_cases hx16 : x ≤ 16
            · exact below_square_B_core_10_16 hx10' hx16
            · have hx16' : 16 ≤ x := by linarith
              by_cases hx24 : x ≤ 24
              · exact below_square_B_core_16_24 hx16' hx24
              · have hx24' : 24 ≤ x := by linarith
                exact below_square_B_core_24_31 hx24' hx31

theorem below_square_B_core_large {K x : ℝ}
    (_hK120 : 120 ≤ K) (hx31 : 31 ≤ x) (hxhi : x ≤ K / 4 + 1) :
    Real.sqrt (x / K) / 3 * Real.log (K * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hxpos : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  let K0 : ℝ := 4 * x - 4
  have hK0pos : 0 < K0 := by
    dsimp [K0]
    linarith
  have hK0K : K0 ≤ K := by
    dsimp [K0]
    linarith
  have hexp : Real.exp 2 ≤ K0 * x := by
    have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hexp1pos : 0 < Real.exp 1 := Real.exp_pos 1
    have hexp2 : Real.exp 2 < 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    dsimp [K0]
    nlinarith
  have hmono :=
    sqrt_div_mul_log_mul_le_of_base_le
      (K0 := K0) (K := K) (x := x) hK0pos hK0K hxpos hexp
  have hmono_div :
      Real.sqrt (x / K) / 3 * Real.log (K * x)
        ≤ Real.sqrt (x / K0) / 3 * Real.log (K0 * x) := by
    have h3 : (0 : ℝ) ≤ 3 := by norm_num
    have h := div_le_div_of_nonneg_right hmono h3
    convert h using 1 <;> ring
  have hsqrt : Real.sqrt (x / K0) ≤ (13 : ℝ) / 25 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ (13 : ℝ) / 25)]
    dsimp [K0]
    have hdenpos : 0 < (4 : ℝ) * x - 4 := by nlinarith
    rw [div_le_iff₀ hdenpos]
    nlinarith [hx31]
  have hlogbase :
      Real.log (K0 * x) ≤ Real.log 4 + 2 * Real.log x := by
    have hbasepos : 0 < K0 * x := mul_pos hK0pos hxpos
    have hlearg : K0 * x ≤ 4 * x ^ 2 := by
      dsimp [K0]
      nlinarith
    have hlogle := Real.log_le_log hbasepos hlearg
    have hrewrite : Real.log (4 * x ^ 2) = Real.log 4 + 2 * Real.log x := by
      have hx_ne : x ≠ 0 := ne_of_gt hxpos
      have hx2_ne : x ^ 2 ≠ 0 := pow_ne_zero 2 hx_ne
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx2_ne, Real.log_pow]
      norm_num
    linarith
  have hlogbase_nonneg : 0 ≤ Real.log (K0 * x) := by
    have hbase_one : (1 : ℝ) ≤ K0 * x := by
      dsimp [K0]
      nlinarith
    exact Real.log_nonneg hbase_one
  have hterm_base :
      Real.sqrt (x / K0) / 3 * Real.log (K0 * x)
        ≤ ((13 : ℝ) / 25) / 3 * (Real.log 4 + 2 * Real.log x) := by
    have hmul := mul_le_mul hsqrt hlogbase hlogbase_nonneg (by norm_num : (0 : ℝ) ≤ (13 : ℝ) / 25)
    nlinarith
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hminlog : min 1 (x / 3) * Real.log 4 ≤ (7 : ℝ) / 5 := by
    calc
      min 1 (x / 3) * Real.log 4 ≤ 1 * Real.log 4 := by
        exact mul_le_mul_of_nonneg_right (min_le_left 1 (x / 3)) hlog4_nonneg
      _ ≤ (7 : ℝ) / 5 := by nlinarith [log4_lt_7_5]
  have hlogx : (69 : ℝ) / 25 ≤ Real.log x := by
    have hlelog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by linarith : (16 : ℝ) ≤ x)
    nlinarith [hlelog, log16_gt_69_25]
  have hinv : 1 / x ≤ (1 : ℝ) / 31 := by
    exact one_div_le_one_div_of_le (by norm_num) hx31
  have haux :
      ((13 : ℝ) / 25) / 3 * (Real.log 4 + 2 * Real.log x) + (7 : ℝ) / 5 + (1 : ℝ) / 32
        ≤ Real.log x + 1 - 1 / x := by
    nlinarith [log4_lt_7_5, hlogx, hinv]
  have hlower := entropyRatio_lower_log_add hx1
  linarith

theorem below_square_B_core {K x : ℝ}
    (hK120 : 120 ≤ K) (hx2 : 2 ≤ x) (hxhi : x ≤ K / 4 + 1) :
    Real.sqrt (x / K) / 3 * Real.log (K * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1) := by
  by_cases hx31 : x ≤ 31
  · have hmono :=
      sqrt_div_mul_log_mul_le_of_120_le (K := K) (x := x) hK120 hx2
    have hmono_div :
        Real.sqrt (x / K) / 3 * Real.log (K * x)
          ≤ Real.sqrt (x / 120) / 3 * Real.log (120 * x) := by
      have h3 : (0 : ℝ) ≤ 3 := by norm_num
      have h := div_le_div_of_nonneg_right hmono h3
      convert h using 1 <;> ring
    have hcompact := below_square_B_core_compact hx2 hx31
    linarith
  · have hx31' : 31 ≤ x := by linarith
    exact below_square_B_core_large hK120 hx31' hxhi

theorem below_square_far_theta_gap_of_120_le
    {n k : ℕ} (hk120 : 120 ≤ k) (hn2k : 2 * k ≤ n)
    (_hnsq : n < k * k) (hfar : 2 * sqrt n < min k (n / 3)) :
    ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4
        - Chebyshev.theta ((sqrt n : ℕ) : ℝ) <
      entropyTerm n k
        + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
        + Real.log (2 * Real.pi) / 2 - 2 := by
  let x : ℝ := (n : ℝ) / (k : ℝ)
  let M : ℕ := min k (n / 3)
  have hkpos : 0 < k := by omega
  have hklt : k < n := by omega
  have hkposR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hkneR : (k : ℝ) ≠ 0 := ne_of_gt hkposR
  have hn_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hx2 : 2 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hkposR]
    exact_mod_cast hn2k
  have hfar_k : 2 * sqrt n < k :=
    lt_of_lt_of_le hfar (min_le_left k (n / 3))
  have hxhi : x ≤ (k : ℝ) / 4 + 1 := by
    have hroot : (n : ℝ) < ((sqrt n : ℝ) + 1) ^ 2 := by
      have h := Nat.lt_succ_sqrt' n
      exact_mod_cast h
    have h2root : 2 * ((sqrt n : ℝ) + 1) ≤ (k : ℝ) + 1 := by
      exact_mod_cast (by omega : 2 * (sqrt n + 1) ≤ k + 1)
    have hsquare :
        ((sqrt n : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 / 4 := by
      nlinarith [sq_nonneg ((k : ℝ) + 1 - 2 * ((sqrt n : ℝ) + 1))]
    have hn_bound : (n : ℝ) ≤ ((k : ℝ) / 4 + 1) * (k : ℝ) := by
      have hn_bound0 : (n : ℝ) ≤ ((k : ℝ) + 1) ^ 2 / 4 :=
        le_trans hroot.le hsquare
      nlinarith [hkposR]
    dsimp [x]
    exact (div_le_iff₀ hkposR).mpr hn_bound
  have hlogkx_eq : Real.log ((k : ℝ) * x) = Real.log n := by
    congr 1
    dsimp [x]
    field_simp [hkneR]
  have hlogkx_nonneg : 0 ≤ Real.log ((k : ℝ) * x) := by
    rw [hlogkx_eq]
    exact Real.log_nonneg hn_ge_one
  have hsqrt_ratio := nat_sqrt_div_le_sqrt_ratio (n := n) (k := k) hkpos
  have hsqrt_term :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        ≤ (k : ℝ) * (Real.sqrt (x / (k : ℝ)) / 3 * Real.log ((k : ℝ) * x)) := by
    have hcoeff_nonneg : 0 ≤ (k : ℝ) * Real.log ((k : ℝ) * x) / 3 := by
      have hmul : 0 ≤ (k : ℝ) * Real.log ((k : ℝ) * x) :=
        mul_nonneg hkposR.le hlogkx_nonneg
      nlinarith
    calc
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          = (((sqrt n : ℕ) : ℝ) / (k : ℝ))
              * ((k : ℝ) * Real.log ((k : ℝ) * x) / 3) := by
              rw [hlogkx_eq]
              field_simp [hkneR]
      _ ≤ Real.sqrt (x / (k : ℝ)) * ((k : ℝ) * Real.log ((k : ℝ) * x) / 3) := by
              exact mul_le_mul_of_nonneg_right hsqrt_ratio hcoeff_nonneg
      _ = (k : ℝ) * (Real.sqrt (x / (k : ℝ)) / 3 * Real.log ((k : ℝ) * x)) := by
              ring
  have hM_le_k : M ≤ k := min_le_left k (n / 3)
  have hM_le_n_div3 : M * 3 ≤ n := by
    have hM : M ≤ n / 3 := min_le_right k (n / 3)
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp hM
  have hMratio_left : ((M : ℕ) : ℝ) / (k : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hkposR]
    have hMk : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hM_le_k
    nlinarith
  have hMratio_right : ((M : ℕ) : ℝ) / (k : ℝ) ≤ x / 3 := by
    rw [div_le_iff₀ hkposR]
    have hMreal : (M : ℝ) ≤ (n : ℝ) / 3 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      exact_mod_cast hM_le_n_div3
    have hxmul : x / 3 * (k : ℝ) = (n : ℝ) / 3 := by
      dsimp [x]
      field_simp [hkneR]
    nlinarith
  have hMratio : ((M : ℕ) : ℝ) / (k : ℝ) ≤ min 1 (x / 3) :=
    le_min hMratio_left hMratio_right
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hM_term :
      ((M : ℕ) : ℝ) * Real.log 4
        ≤ (k : ℝ) * (min 1 (x / 3) * Real.log 4) := by
    calc
      ((M : ℕ) : ℝ) * Real.log 4
          = (((M : ℕ) : ℝ) / (k : ℝ)) * ((k : ℝ) * Real.log 4) := by
              field_simp [hkneR]
      _ ≤ min 1 (x / 3) * ((k : ℝ) * Real.log 4) := by
              exact mul_le_mul_of_nonneg_right hMratio (mul_nonneg hkposR.le hlog4_nonneg)
      _ = (k : ℝ) * (min 1 (x / 3) * Real.log 4) := by
              ring
  have hcore := below_square_B_core (K := (k : ℝ)) (x := x)
    (by exact_mod_cast hk120) hx2 hxhi
  have hentropy_core :
      (k : ℝ) *
        (Real.sqrt (x / (k : ℝ)) / 3 * Real.log ((k : ℝ) * x)
          + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32)
        ≤ entropyTerm n k := by
    have hmul := mul_le_mul_of_nonneg_left hcore hkposR.le
    rw [entropyTerm_eq_mul_entropyRatio (n := n) (k := k) hkpos hklt]
    exact hmul
  have hupper_plus :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((M : ℕ) : ℝ) * Real.log 4 + (k : ℝ) / 32
        ≤ entropyTerm n k := by
    have hsum :
        ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
            + ((M : ℕ) : ℝ) * Real.log 4 + (k : ℝ) / 32
          ≤ (k : ℝ) *
            (Real.sqrt (x / (k : ℝ)) / 3 * Real.log ((k : ℝ) * x)
              + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32) := by
      nlinarith [hsqrt_term, hM_term]
    exact hsum.trans hentropy_core
  have htail := large_k_stirling_tail_lt_div32 hk120
  have hcorr := stirling_correction_ge_neg_log_k_sub_six_fifths (n := n) (k := k) hkpos hklt
  have htheta_nonneg : 0 ≤ Chebyshev.theta ((sqrt n : ℕ) : ℝ) :=
    Chebyshev.theta_nonneg _
  dsimp [M] at hupper_plus
  nlinarith

theorem exists_large_prime_factor_choose_below_sq_far_of_120_le
    {n k : ℕ} (hk120 : 120 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : 33 ≤ sqrt n)
    (hfar : 2 * sqrt n < min k (n / 3)) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hkpos : 0 < k := by omega
  have hklt : k < n := by omega
  have hn6 : 6 ≤ n := by
    have hsqrt_le_self : sqrt n ≤ n := Nat.sqrt_le_self n
    omega
  have hsqrtM : sqrt n ≤ min k (n / 3) := by omega
  have hgap :=
    below_square_far_theta_gap_of_120_le
      (n := n) (k := k) hk120 hn2k hnsq hfar
  exact exists_large_prime_factor_choose_of_theta_interval_entropy_gap
    hkpos hklt hn2k hn6 hsqrt33 hsqrtM hgap

set_option maxHeartbeats 800000 in
theorem exists_large_prime_factor_choose_below_sq_close_of_sqrt33
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : 33 ≤ sqrt n)
    (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hkpos : 0 < k := by omega
  have hkn : k ≤ n := by omega
  have hklt : k < n := by omega
  have hnpos : 0 < n := hkpos.trans_le hkn
  have hn6 : 6 ≤ n := by
    have hsqrt_le_self : sqrt n ≤ n := Nat.sqrt_le_self n
    omega
  have hn9 : 9 ≤ n := by omega
  have hsqrtM : sqrt n ≤ min k (n / 3) :=
    sqrt_le_min_of_nine_le_and_lt_sq hn9 hnsq
  have hM_eq : min k (n / 3) = k :=
    min_eq_left_of_sqrt33_close hsqrt33 hMsub
  have hsqrt_lt_k : sqrt n < k := Nat.sqrt_lt.mpr hnsq
  have hk34 : 34 ≤ k := by omega
  have hk_le_2sqrt : k ≤ 2 * sqrt n := by
    rw [hM_eq] at hMsub
    omega
  have hksq4 : k * k ≤ 4 * n := by
    have hsq : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
    nlinarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt_one : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hlogn_pos : 0 < Real.log n := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogk_le_logn : Real.log k ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hkpos) (by exact_mod_cast hkn)
  have hnkpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hlognk_le_logn : Real.log (n - k) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hnkpos) (by exact_mod_cast (by omega : n - k ≤ n))
  have hlogtwopi_nonneg : 0 ≤ Real.log (2 * Real.pi) := by
    exact Real.log_nonneg (by nlinarith [Real.one_le_pi_div_two])
  have hcorr_ge :
      - Real.log n / 2 - 2 ≤
        Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
          + Real.log (2 * Real.pi) / 2 - 2 := by
    nlinarith
  have hlog4_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have htwologk_le : 2 * Real.log k ≤ Real.log n + 2 * Real.log 2 := by
    have hlog_sq_le : Real.log ((k : ℝ) ^ 2) ≤ Real.log ((4 : ℝ) * (n : ℝ)) := by
      have hcast : (k : ℝ) ^ 2 ≤ (4 : ℝ) * (n : ℝ) := by
        norm_num [pow_two]
        exact_mod_cast hksq4
      exact Real.log_le_log (sq_pos_of_pos (by exact_mod_cast hkpos)) hcast
    rw [Real.log_pow] at hlog_sq_le
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by exact_mod_cast hnpos.ne' : (n : ℝ) ≠ 0), hlog4_eq] at hlog_sq_le
    norm_num at hlog_sq_le
    nlinarith
  have hlogk_le_half : Real.log k ≤ Real.log n / 2 + Real.log 2 := by
    linarith
  have hk_sq_div_le_four : (k : ℝ) ^ 2 / (n : ℝ) ≤ 4 := by
    have hcast : (k : ℝ) ^ 2 ≤ 4 * (n : ℝ) := by
      norm_num [pow_two]
      exact_mod_cast hksq4
    exact (div_le_iff₀ (by exact_mod_cast hnpos : (0 : ℝ) < n)).mpr (by linarith)
  have hbasic_ge :
      (k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4 ≤
        (k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ) := by
    have hmul : (k : ℝ) * Real.log k ≤ (k : ℝ) * (Real.log n / 2 + Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogk_le_half (by positivity)
    nlinarith
  have hbasic_ge_shift :
      ((k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4)
          - Real.log n / 2 - (2 : ℝ) ≤
        ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - (2 : ℝ) := by
    exact close_branch_shift_aux hbasic_ge
  have hlog16_lt_four : Real.log (16 : ℝ) < 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    nlinarith
  have hlogk_le_six : Real.log k ≤ (k : ℝ) / 6 := by
    have hdivpos : 0 < (k : ℝ) / 16 := by positivity
    have hdiv :=
      Real.log_le_sub_one_of_pos (x := (k : ℝ) / 16) hdivpos
    rw [Real.log_div (by exact_mod_cast hkpos.ne' : (k : ℝ) ≠ 0)
      (by norm_num : (16 : ℝ) ≠ 0)] at hdiv
    have haux : Real.log k ≤ (k : ℝ) / 16 + 3 := by
      nlinarith
    have hk34r : (34 : ℝ) ≤ k := by exact_mod_cast hk34
    nlinarith
  have hlogn_lt_twologk : Real.log n < 2 * Real.log k := by
    have hlog_lt : Real.log (n : ℝ) < Real.log ((k * k : ℕ) : ℝ) :=
      Real.log_lt_log (by exact_mod_cast hnpos) (by exact_mod_cast hnsq)
    rw [show ((k * k : ℕ) : ℝ) = (k : ℝ) ^ 2 by norm_num [pow_two],
      Real.log_pow] at hlog_lt
    exact hlog_lt
  have hlogn_le_kthird : Real.log n ≤ (k : ℝ) / 3 := by
    linarith only [hlogn_lt_twologk, hlogk_le_six]
  have hlogn_half_le_ksix : Real.log n / 2 ≤ (k : ℝ) / 6 := by
    linarith only [hlogn_le_kthird]
  have hn1024 : 1024 < n := by
    have hsq : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
    have h1024 : 1024 < sqrt n * sqrt n := by
      nlinarith only [hsqrt33]
    exact h1024.trans_le hsq
  have hten_log2_lt_logn : 10 * Real.log 2 < Real.log n := by
    have hlog_lt : Real.log (1024 : ℝ) < Real.log (n : ℝ) :=
      Real.log_lt_log (by norm_num) (by exact_mod_cast hn1024)
    rwa [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow] at hlog_lt
  have hcoef : (2 : ℝ) / 3 < Real.log n / 6 - 2 * Real.log 2 + 1 := by
    exact close_branch_coef_gap_aux hten_log2_lt_logn hlog2_lt_one
  have hmain :
      0 < (k : ℝ) * (Real.log n / 6 - 2 * Real.log 2 + 1)
          - Real.log n / 2 - 6 := by
    have hk34r : (34 : ℝ) ≤ k := by exact_mod_cast hk34
    exact close_branch_main_gap_aux hk34r hlogn_half_le_ksix hcoef
  have hsimple_gap :
      (k : ℝ) / 3 * Real.log n + (k : ℝ) * Real.log 2 <
        ((k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4)
          - Real.log n / 2 - 2 := by
    exact close_branch_simple_gap_aux hmain
  have hupper_simple :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 ≤
        (k : ℝ) / 3 * Real.log n + (k : ℝ) * Real.log 2 := by
    exact close_branch_upper_simple_aux
      (a := sqrt n) (k := k) (M := min k (n / 3))
      (N := Real.log n) (L := Real.log 2) hM_eq hsqrt_lt_k.le hlogn_pos.le
  have hbasic := entropyTerm_lower_basic (n := n) (k := k) hkpos hklt
  have hlower_entropy := entropy_lower_le_log_choose (n := n) (k := k) hkpos hklt
  have hlower :
      ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2
        ≤ Real.log (n.choose k) := by
    calc
      ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2
          ≤ entropyTerm n k
            + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
            + Real.log (2 * Real.pi) / 2 - 2 := by
              linarith only [hbasic, hcorr_ge]
      _ ≤ Real.log (n.choose k) := hlower_entropy
  have hupper_lt_lower :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 <
        ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2 := by
    calc
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2
          ≤ (k : ℝ) / 3 * Real.log n + (k : ℝ) * Real.log 2 := hupper_simple
      _ < (k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4
            - Real.log n / 2 - 2 := hsimple_gap
      _ ≤ ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2 := by
            exact hbasic_ge_shift
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hupper :=
    log_choose_le_sqrt_third_log_add_min_third_log_two_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrt33 hsqrtM hMsub
  exact not_lt_of_ge (hlower.trans hupper) hupper_lt_lower

theorem exists_large_prime_factor_choose_sq_le_of_9_le
    {n k : ℕ} (hk9 : 9 ≤ k) (hkn : k ≤ n) (hsq : k * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) :=
  exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
    (by omega) hkn hsq (primeCounting_gap_of_9_le hk9)





theorem exists_large_prime_factor_choose_small_cert :
    ∀ k : Fin 9, ∀ n : Fin 94,
      0 < k.val → 2 * k.val ≤ n.val →
        ∃ p : Fin 94, k.val < p.val ∧ p.val.Prime ∧ p.val ∣ n.val.choose k.val := by
  set_option maxRecDepth 10000 in
  decide

theorem pow_gap_small_k_tail {n k : ℕ} (hkpos : 0 < k) (hk9 : k < 9) (hn94 : 94 ≤ n) :
    k ^ k < n ^ (k - Nat.primeCounting k) := by
  interval_cases k
  · exact lt_of_lt_of_le
      (by decide : 1 ^ 1 < 94 ^ (1 - Nat.primeCounting 1))
      (Nat.pow_le_pow_left hn94 (1 - Nat.primeCounting 1))
  · exact lt_of_lt_of_le
      (by decide : 2 ^ 2 < 94 ^ (2 - Nat.primeCounting 2))
      (Nat.pow_le_pow_left hn94 (2 - Nat.primeCounting 2))
  · exact lt_of_lt_of_le
      (by decide : 3 ^ 3 < 94 ^ (3 - Nat.primeCounting 3))
      (Nat.pow_le_pow_left hn94 (3 - Nat.primeCounting 3))
  · exact lt_of_lt_of_le
      (by decide : 4 ^ 4 < 94 ^ (4 - Nat.primeCounting 4))
      (Nat.pow_le_pow_left hn94 (4 - Nat.primeCounting 4))
  · exact lt_of_lt_of_le
      (by decide : 5 ^ 5 < 94 ^ (5 - Nat.primeCounting 5))
      (Nat.pow_le_pow_left hn94 (5 - Nat.primeCounting 5))
  · exact lt_of_lt_of_le
      (by decide : 6 ^ 6 < 94 ^ (6 - Nat.primeCounting 6))
      (Nat.pow_le_pow_left hn94 (6 - Nat.primeCounting 6))
  · exact lt_of_lt_of_le
      (by decide : 7 ^ 7 < 94 ^ (7 - Nat.primeCounting 7))
      (Nat.pow_le_pow_left hn94 (7 - Nat.primeCounting 7))
  · exact lt_of_lt_of_le
      (by decide : 8 ^ 8 < 94 ^ (8 - Nat.primeCounting 8))
      (Nat.pow_le_pow_left hn94 (8 - Nat.primeCounting 8))

theorem exists_large_prime_factor_choose_of_lt_9
    {n k : ℕ} (hkpos : 0 < k) (hk9 : k < 9) (hn2k : 2 * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_cases hn94 : n < 94
  · rcases exists_large_prime_factor_choose_small_cert ⟨k, hk9⟩ ⟨n, hn94⟩
      hkpos hn2k with ⟨p, hkp, hp, hpdvd⟩
    exact ⟨p.val, hkp, hp, hpdvd⟩
  · exact exists_large_prime_factor_choose_of_pow_gap (n := n) (k := k)
      hkpos (by omega) (by interval_cases k <;> decide)
      (pow_gap_small_k_tail hkpos hk9 (by omega))







/--
Factorial form of the standard binomial-divisibility argument: if a prime
divides `n!` but not the two factorial factors in
`C(n,k) * k! * (n-k)! = n!`, then it divides `C(n,k)`.
-/
theorem prime_dvd_choose_of_dvd_factorial_not_factorial_sides {n k p : ℕ}
    (hkn : k ≤ n) (hp : p.Prime) (hdvd : p ∣ n !)
    (hk : ¬ p ∣ k !) (hnk : ¬ p ∣ (n - k) !) : p ∣ n.choose k := by
  have h_eq : n.choose k * k ! * (n - k) ! = n ! :=
    choose_mul_factorial_mul_factorial hkn
  rw [← h_eq] at hdvd
  have hleft : p ∣ n.choose k * k ! := (hp.dvd_mul.mp hdvd).resolve_right hnk
  exact (hp.dvd_mul.mp hleft).resolve_right hk

theorem prime_not_dvd_factorial_of_lt {p k : ℕ} (hp : p.Prime) (hk : k < p) :
    ¬ p ∣ k ! := by
  rwa [hp.dvd_factorial, not_le]





























/--
If a prime divisor of `n!` is larger than both factorial factors
`k!` and `(n-k)!`, then it must appear in the binomial coefficient.
This is the form used by the central Bertrand-prime argument, and it is
also the local step needed in the general Sylvester proof.
-/
theorem prime_dvd_choose_of_interval_prime {n k p : ℕ} (hkn : k ≤ n)
    (hp : p.Prime) (hk : k < p) (hnk : n - k < p) (hpn : p ≤ n) :
    p ∣ n.choose k :=
  prime_dvd_choose_of_dvd_factorial_not_factorial_sides hkn hp
    (hp.dvd_factorial.mpr hpn)
    (prime_not_dvd_factorial_of_lt hp hk)
    (prime_not_dvd_factorial_of_lt hp hnk)

theorem hasPrimeFactorAbove_choose_of_interval_prime {n k p : ℕ} (hkn : k ≤ n)
    (hp : p.Prime) (hk : k < p) (hnk : n - k < p) (hpn : p ≤ n) :
    HasPrimeFactorAbove k (n.choose k) :=
  ⟨p, hk, hp, prime_dvd_choose_of_interval_prime hkn hp hk hnk hpn⟩

theorem exists_large_prime_factor_choose_125_12 :
    HasPrimeFactorAbove 12 ((125).choose 12) := by
  refine ⟨13, by norm_num, by norm_num, ?_⟩
  set_option maxRecDepth 10000 in
  decide

theorem exists_large_prime_factor_choose_126_12 :
    HasPrimeFactorAbove 12 ((126).choose 12) := by
  refine ⟨13, by norm_num, by norm_num, ?_⟩
  set_option maxRecDepth 10000 in
  decide

theorem exists_large_prime_factor_choose_126_13 :
    HasPrimeFactorAbove 13 ((126).choose 13) := by
  refine ⟨17, by norm_num, by norm_num, ?_⟩
  set_option maxRecDepth 10000 in
  decide





theorem exists_prime_within_of_primeGapCoverWith {gap limit prev m : ℕ} {ps : List ℕ}
    (hcover : PrimeGapCoverWith gap limit prev ps) (hprev : prev ≤ m) (hm : m < limit) :
    ∃ p, m < p ∧ p ≤ m + gap ∧ p.Prime := by
  induction ps generalizing prev with
  | nil => cases hcover
  | cons p ps ih =>
      dsimp [PrimeGapCoverWith] at hcover
      rcases hcover with ⟨hpprime, hp_le, htail⟩
      by_cases hmp : m < p
      · exact ⟨p, hmp, by omega, hpprime⟩
      · have hp_m : p ≤ m := by omega
        rcases htail with hlimitp | hcover_tail
        · omega
        · exact ih hcover_tail hp_m



theorem primeGap20Cover_cert : PrimeGapCoverWith 20 1089 0 primeGap20Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGap20Cover]

theorem exists_prime_within_20_of_lt_1089 {m : ℕ} (hm : m < 1089) :
    ∃ p, m < p ∧ p ≤ m + 20 ∧ p.Prime :=
  exists_prime_within_of_primeGapCoverWith primeGap20Cover_cert (by omega) hm


theorem primeGapSmall9Cover_cert : PrimeGapCoverWith 9 72 9 primeGapSmall9Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall9Cover]


theorem primeGapSmall10Cover_cert : PrimeGapCoverWith 10 90 10 primeGapSmall10Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall10Cover]


theorem primeGapSmall11Cover_cert : PrimeGapCoverWith 11 110 11 primeGapSmall11Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall11Cover]


theorem primeGapSmall12_lowCover_cert : PrimeGapCoverWith 12 113 12 primeGapSmall12_lowCover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall12_lowCover]


theorem primeGapSmall12_highCover_cert : PrimeGapCoverWith 12 132 115 primeGapSmall12_highCover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall12_highCover]


theorem primeGapSmall13_lowCover_cert : PrimeGapCoverWith 13 113 13 primeGapSmall13_lowCover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall13_lowCover]


theorem primeGapSmall13_highCover_cert : PrimeGapCoverWith 13 156 114 primeGapSmall13_highCover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall13_highCover]


theorem primeGapSmall14Cover_cert : PrimeGapCoverWith 14 182 14 primeGapSmall14Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall14Cover]


theorem primeGapSmall15Cover_cert : PrimeGapCoverWith 15 210 15 primeGapSmall15Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall15Cover]


theorem primeGapSmall16Cover_cert : PrimeGapCoverWith 16 240 16 primeGapSmall16Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall16Cover]


theorem primeGapSmall17Cover_cert : PrimeGapCoverWith 17 272 17 primeGapSmall17Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall17Cover]


theorem primeGapSmall18Cover_cert : PrimeGapCoverWith 18 306 18 primeGapSmall18Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall18Cover]


theorem primeGapSmall19Cover_cert : PrimeGapCoverWith 19 342 19 primeGapSmall19Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall19Cover]


theorem primeGapSmall34Cover_cert : PrimeGapCoverWith 34 1122 34 primeGapSmall34Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall34Cover]


theorem primeGapSmall35Cover_cert : PrimeGapCoverWith 35 1190 35 primeGapSmall35Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCoverWith, primeGapSmall35Cover]

theorem exists_interval_prime_or_exception_of_9_le_lt_20
    {n k : ℕ} (hk9 : 9 ≤ k) (hk20 : k < 20) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) :
    (∃ p, k < p ∧ n - k < p ∧ p ≤ n ∧ p.Prime)
      ∨ (n = 125 ∧ k = 12)
      ∨ (n = 126 ∧ k = 12)
      ∨ (n = 126 ∧ k = 13) := by
  interval_cases k
  ·
    have hmlo : 9 ≤ n - 9 := by omega
    have hmlimit : n - 9 < 72 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall9Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 10 ≤ n - 10 := by omega
    have hmlimit : n - 10 < 90 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall10Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 11 ≤ n - 11 := by omega
    have hmlimit : n - 11 < 110 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall11Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 12 ≤ n - 12 := by omega
    by_cases hm113 : n - 12 = 113
    · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
    by_cases hm114 : n - 12 = 114
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))
    by_cases hlow : n - 12 < 113
    · obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
        primeGapSmall12_lowCover_cert hmlo hlow
      left
      exact ⟨p, by omega, hmp, by omega, hpprime⟩
    · have hmhigh : 115 ≤ n - 12 := by omega
      have hmlimit : n - 12 < 132 := by omega
      obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
        primeGapSmall12_highCover_cert hmhigh hmlimit
      left
      exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 13 ≤ n - 13 := by omega
    by_cases hm113 : n - 13 = 113
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))
    by_cases hlow : n - 13 < 113
    · obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
        primeGapSmall13_lowCover_cert hmlo hlow
      left
      exact ⟨p, by omega, hmp, by omega, hpprime⟩
    · have hmhigh : 114 ≤ n - 13 := by omega
      have hmlimit : n - 13 < 156 := by omega
      obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
        primeGapSmall13_highCover_cert hmhigh hmlimit
      left
      exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 14 ≤ n - 14 := by omega
    have hmlimit : n - 14 < 182 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall14Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 15 ≤ n - 15 := by omega
    have hmlimit : n - 15 < 210 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall15Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 16 ≤ n - 16 := by omega
    have hmlimit : n - 16 < 240 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall16Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 17 ≤ n - 17 := by omega
    have hmlimit : n - 17 < 272 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall17Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 18 ≤ n - 18 := by omega
    have hmlimit : n - 18 < 306 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall18Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 19 ≤ n - 19 := by omega
    have hmlimit : n - 19 < 342 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall19Cover_cert hmlo hmlimit
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩

theorem exists_interval_prime_of_34_le_lt_36
    {n k : ℕ} (hk34 : 34 ≤ k) (hk36 : k < 36) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) :
    ∃ p, k < p ∧ n - k < p ∧ p ≤ n ∧ p.Prime := by
  interval_cases k
  ·
    have hmlo : 34 ≤ n - 34 := by omega
    have hmlimit : n - 34 < 1122 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall34Cover_cert hmlo hmlimit
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  ·
    have hmlo : 35 ≤ n - 35 := by omega
    have hmlimit : n - 35 < 1190 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_of_primeGapCoverWith
      primeGapSmall35Cover_cert hmlo hmlimit
    exact ⟨p, by omega, hmp, by omega, hpprime⟩

theorem nextPrimeAfter1089_below_sq_sqrt_lt_33_cert :
    ∀ k : Fin 545, ∀ n : Fin 1089,
      9 ≤ k.val → 2 * k.val ≤ n.val → n.val < k.val * k.val →
        (∃ p, k.val < p ∧ n.val - k.val < p ∧ p ≤ n.val ∧ p.Prime)
        ∨ (n.val = 125 ∧ k.val = 12)
        ∨ (n.val = 126 ∧ k.val = 12)
        ∨ (n.val = 126 ∧ k.val = 13) := by
  intro k n hk9 hn2k hnsq
  by_cases hk20 : 20 ≤ k.val
  · have hm_lt : n.val - k.val < 1089 := by omega
    obtain ⟨p, hmp, hp_le, hpprime⟩ := exists_prime_within_20_of_lt_1089 hm_lt
    left
    exact ⟨p, by omega, hmp, by omega, hpprime⟩
  · have hklt20 : k.val < 20 := by omega
    exact exists_interval_prime_or_exception_of_9_le_lt_20 hk9 hklt20 hn2k hnsq

theorem exists_large_prime_factor_choose_below_sq_of_sqrt_lt_33
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : sqrt n < 33) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hn1089 : n < 1089 := by
    rw [Nat.sqrt_lt] at hsqrt33
    simpa using hsqrt33
  have hk545 : k < 545 := by nlinarith
  rcases nextPrimeAfter1089_below_sq_sqrt_lt_33_cert
      ⟨k, hk545⟩ ⟨n, hn1089⟩ hk9 hn2k hnsq with
    (⟨p, hkp, hnkp, hpn, hp⟩ | ⟨hn, hk⟩ | ⟨hn, hk⟩ | ⟨hn, hk⟩)
  · exact hasPrimeFactorAbove_choose_of_interval_prime (by omega : k ≤ n) hp hkp hnkp hpn
  · have hn' : n = 125 := by simpa using hn
    have hk' : k = 12 := by simpa using hk
    subst n
    subst k
    exact exists_large_prime_factor_choose_125_12
  · have hn' : n = 126 := by simpa using hn
    have hk' : k = 12 := by simpa using hk
    subst n
    subst k
    exact exists_large_prime_factor_choose_126_12
  · have hn' : n = 126 := by simpa using hn
    have hk' : k = 13 := by simpa using hk
    subst n
    subst k
    exact exists_large_prime_factor_choose_126_13



theorem nextPrimeWithin_spec {fuel m p : ℕ} (hp : p.Prime) (hmp : m < p)
    (hpfuel : p ≤ m + fuel) :
    let q := nextPrimeWithin fuel m
    m < q ∧ q ≤ p ∧ q.Prime := by
  induction fuel generalizing m with
  | zero => omega
  | succ fuel ih =>
      dsimp [nextPrimeWithin]
      by_cases hp1 : Nat.Prime (m + 1)
      · simp [hp1]
        omega
      · simp [hp1]
        have hm1p : m + 1 < p := by
          have hm1le : m + 1 ≤ p := by omega
          exact lt_of_le_of_ne hm1le (by
            intro hEq
            apply hp1
            simpa [hEq] using hp)
        have hpfuel' : p ≤ (m + 1) + fuel := by omega
        rcases ih hm1p hpfuel' with ⟨hq_gt, hq_le, hq_prime⟩
        exact ⟨by omega, hq_le, hq_prime⟩





theorem exists_prime_within_of_primeGapCover {limit prev m : ℕ} {ps : List ℕ}
    (hcover : PrimeGapCover limit prev ps) (hprev : prev ≤ m) (hm : m < limit) :
    ∃ p, m < p ∧ p ≤ m + 36 ∧ p.Prime := by
  induction ps generalizing prev with
  | nil => cases hcover
  | cons p ps ih =>
      dsimp [PrimeGapCover] at hcover
      rcases hcover with ⟨hpprime, hp_le, htail⟩
      by_cases hmp : m < p
      · exact ⟨p, hmp, by omega, hpprime⟩
      · have hp_m : p ≤ m := by omega
        rcases htail with hlimitp | hcover_tail
        · omega
        · exact ih hcover_tail hp_m

theorem primeGap36Cover_cert : PrimeGapCover 14400 0 primeGap36Cover := by
  set_option maxRecDepth 10000 in
  norm_num [PrimeGapCover, primeGap36Cover]

theorem exists_prime_within_36_of_lt_14400 {m : ℕ} (hm : m < 14400) :
    ∃ p, m < p ∧ p ≤ m + 36 ∧ p.Prime :=
  exists_prime_within_of_primeGapCover primeGap36Cover_cert (by omega) hm

theorem interval_prime_below_sq_k_lt_120_sqrt33_cert :
    ∀ k : Fin 120, ∀ n : Fin 14400,
      9 ≤ k.val → 33 ≤ sqrt n.val → 2 * k.val ≤ n.val → n.val < k.val * k.val →
        let p := nextPrimeWithin 36 (n.val - k.val)
        k.val < p ∧ n.val - k.val < p ∧ p ≤ n.val ∧ Nat.Prime p := by
  intro k n _hk9 hsqrt hn2k hnsq
  have hm_lt : n.val - k.val < 14400 := by omega
  obtain ⟨r, hmr, hr_le, hrprime⟩ := exists_prime_within_36_of_lt_14400 hm_lt
  have hnext := nextPrimeWithin_spec (fuel := 36) (m := n.val - k.val) (p := r)
    hrprime hmr hr_le
  dsimp only at hnext ⊢
  rcases hnext with ⟨hnext_gt, hnext_le, hnext_prime⟩
  have hkle : k.val ≤ n.val - k.val := by omega
  have hkp : k.val < nextPrimeWithin 36 (n.val - k.val) := lt_of_le_of_lt hkle hnext_gt
  have hpn : nextPrimeWithin 36 (n.val - k.val) ≤ n.val := by
    by_cases hk36 : 36 ≤ k.val
    · have hp_le : nextPrimeWithin 36 (n.val - k.val) ≤ (n.val - k.val) + 36 := by
        exact hnext_le.trans hr_le
      omega
    · have hklt36 : k.val < 36 := by omega
      have hn1089 : 1089 ≤ n.val := by
        simpa using (Nat.le_sqrt.mp hsqrt)
      have hk34 : 34 ≤ k.val := by
        by_contra hk34not
        have hkle33 : k.val ≤ 33 := by omega
        have hsq_le : k.val * k.val ≤ 33 * 33 := Nat.mul_le_mul hkle33 hkle33
        omega
      obtain ⟨s, _hks, hms, hsn, hsprime⟩ :=
        exists_interval_prime_of_34_le_lt_36 hk34 hklt36 hn2k hnsq
      have hs_fuel : s ≤ (n.val - k.val) + 36 := by omega
      have hs_next := nextPrimeWithin_spec (fuel := 36) (m := n.val - k.val) (p := s)
        hsprime hms hs_fuel
      exact hs_next.2.1.trans hsn
  exact ⟨hkp, hnext_gt, hpn, hnext_prime⟩

theorem exists_large_prime_factor_choose_below_sq_of_k_lt_120
    {n k : ℕ} (hk9 : 9 ≤ k) (hk120 : k < 120) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : 33 ≤ sqrt n) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hn14400 : n < 120 * 120 := by nlinarith
  let p := nextPrimeWithin 36 (n - k)
  have hcert :=
    interval_prime_below_sq_k_lt_120_sqrt33_cert
      ⟨k, hk120⟩ ⟨n, by simpa using hn14400⟩ hk9 hsqrt33 hn2k hnsq
  dsimp only at hcert
  rcases hcert with ⟨hkp, hnkp, hpn, hp⟩
  exact hasPrimeFactorAbove_choose_of_interval_prime (by omega : k ≤ n) hp hkp hnkp hpn

theorem exists_large_prime_factor_choose_below_sq_of_9_le
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n) (hnsq : n < k * k) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_cases hsqrt33_lt : sqrt n < 33
  · exact exists_large_prime_factor_choose_below_sq_of_sqrt_lt_33
      hk9 hn2k hnsq hsqrt33_lt
  · have hsqrt33 : 33 ≤ sqrt n := by omega
    by_cases hk120_lt : k < 120
    · exact exists_large_prime_factor_choose_below_sq_of_k_lt_120
        hk9 hk120_lt hn2k hnsq hsqrt33
    · have hk120 : 120 ≤ k := by omega
      by_cases hclose : min k (n / 3) - sqrt n ≤ sqrt n
      · exact exists_large_prime_factor_choose_below_sq_close_of_sqrt33
          hk9 hn2k hnsq hsqrt33 hclose
      · have hfar : 2 * sqrt n < min k (n / 3) := by omega
        exact exists_large_prime_factor_choose_below_sq_far_of_120_le
          hk120 hn2k hnsq hsqrt33 hfar

theorem exists_large_prime_factor_choose_of_two_mul_le
    {n k : ℕ} (hkpos : 0 < k) (hn2k : 2 * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_cases hk9_lt : k < 9
  · exact exists_large_prime_factor_choose_of_lt_9 hkpos hk9_lt hn2k
  · have hk9 : 9 ≤ k := by omega
    by_cases hsq : k * k ≤ n
    · exact exists_large_prime_factor_choose_sq_le_of_9_le hk9 (by omega) hsq
    · have hbelow : n < k * k := by omega
      exact exists_large_prime_factor_choose_below_sq_of_9_le hk9 hn2k hbelow

/-!
### Central case of Sylvester's theorem

For the central binomial coefficient C(2k,k), we can give a clean proof
using Bertrand's postulate (Chapter 2):
- By Bertrand, ∃ prime p with k < p ≤ 2k.
- p divides (2k)! since p ≤ 2k.
- p does not divide k! since p > k.
- Since C(2k,k) · (k!)² = (2k)!, Euclid's lemma gives p | C(2k,k).
-/



/-!
### General Sylvester's theorem

For n ≥ 2k, the book extends the argument to C(n,k) by analyzing the
product n(n-1)···(n-k+1) = k! · C(n,k). For each of the k consecutive
integers n-j (0 ≤ j ≤ k-1), decompose n-j = q_j · r_j where q_j is
k-smooth and r_j has only prime factors > k. The q_j are bounded by
the prime factorization structure, forcing some r_j > 1.
-/

/--
The general Sylvester theorem: for n ≥ 2k and k ≥ 1, C(n,k) has a prime
divisor exceeding k. The proof reduces to showing the descending factorial
n(n-1)···(n-k+1) is not (k+1)-smooth; the existing infrastructure
(`exists_large_prime_dvd_choose_of_descFactorial_not_smooth`) then gives
the prime factor of C(n,k).
-/
theorem sylvester_general (n k : ℕ) (hn : 2 * k ≤ n) (hk : 0 < k) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k :=
  exists_large_prime_factor_choose_of_two_mul_le hk hn









/-!
### Binomial coefficients are (almost) never powers

Erdős's theorem (1951): C(n,k) ≠ m^l for k ≥ 4, n ≥ 2k, l ≥ 2.
Reference: P. Erdős, On a diophantine equation,
J. London Math. Soc. 26 (1951), 176-178.

Below: Step 1 (concentration lemma + n > k²) is complete.
Steps 2–4 are pending (l-th-power-free decomposition, distinctness,
classification {aⱼ}={1,…,k}, and contradiction for l=2, l≥3).
-/

section Tier1

/-! ### Prime-divisibility helpers for Finset products -/

lemma nat_prime_dvd_finset_prod {p : ℕ} {α : Type _} [DecidableEq α] {s : Finset α}
    {f : α → ℕ} (hp : p.Prime) (h : p ∣ ∏ x ∈ s, f x) : ∃ x ∈ s, p ∣ f x := by
  induction' s using Finset.induction_on with a s' has ih
  · have : p ∣ 1 := by simpa using h
    have hp1 : ¬ p ∣ 1 := by
      intro h1; have := Nat.le_of_dvd (by norm_num) h1; have hpgt1 := hp.one_lt; omega
    exact absurd this hp1
  · rw [Finset.prod_insert has] at h
    rcases hp.dvd_or_dvd h with (hpa | hps')
    · exact ⟨a, Finset.mem_insert_self a s', hpa⟩
    · rcases ih hps' with ⟨x, hx, hpx⟩
      exact ⟨x, Finset.mem_insert_of_mem hx, hpx⟩

lemma nat_prime_not_dvd_finset_prod {p : ℕ} {α : Type _} [DecidableEq α] {s : Finset α}
    {f : α → ℕ} (hp : p.Prime) (h : ∀ x ∈ s, ¬ p ∣ f x) : ¬ p ∣ ∏ x ∈ s, f x := by
  intro hprod; rcases nat_prime_dvd_finset_prod hp hprod with ⟨x, hx, hpx⟩; exact h x hx hpx

/-! ### Step 1: Concentration lemma → n > k² -/

/-- The concentration lemma: if p > k is prime, k ≤ n, and p^l divides
the product of k consecutive integers n, n-1, …, n-k+1,
then all the p-power is in one factor: ∃ i < k, p^l | n - i.

Proof by induction on k with coprimality:
- Base k=0: trivial (p^l ∣ 1 impossible for p > 1).
- Step k→k+1: via n.descFactorial (k+1) = (n−k) * n.descFactorial k.
  - If p ∣ n−k: for any j < k, p ∤ n−j (otherwise p ∣ k−j < p).
    Hence p ∤ n.descFactorial k, so Coprime(p^l, n.descFactorial k)
    forces p^l ∣ n−k.
  - If p ∤ n−k: Coprime(p^l, n−k), so p^l passes through to
    n.descFactorial k. IH gives p^l ∣ n−i for some i < k. -/
lemma pow_l_dvd_one_factor_of_descFactorial {n k l p : ℕ} (hp : p.Prime) (hkp : k < p)
    (hlp : 0 < l) (hk_le_n : k ≤ n) (hp_l_dvd : p ^ l ∣ n.descFactorial k) :
    ∃ i, i < k ∧ p ^ l ∣ n - i := by
  induction k generalizing n with
  | zero =>
      -- k = 0: n.descFactorial 0 = 1, p^l ∣ 1 impossible
      have hp_gt_1 : 1 < p ^ l := by
        calc
          1 = 1 ^ l := by simp
          _ < p ^ l := Nat.pow_lt_pow_left hp.one_lt hlp.ne.symm
      have h1 : p ^ l ∣ 1 := hp_l_dvd
      have hle_p : p ^ l ≤ 1 := Nat.le_of_dvd (by norm_num) h1
      omega
  | succ k ih =>
      -- k → k+1: n.descFactorial (k+1) = (n−k) * n.descFactorial k
      -- In this branch: hkp : k+1 < p, hk_le_n : k+1 ≤ n
      rw [Nat.descFactorial_succ] at hp_l_dvd
      by_cases hdiv_nk : p ∣ n - k
      · -- Case 1: p ∣ n−k. Show ∀ j < k, p ∤ n−j.
        have h_no_other : ∀ j, j < k → ¬ p ∣ n - j := by
          intro j hj
          by_contra! h
          have h_eq : n - j = (n - k) + (k - j) := by
            have : k ≤ n := by omega
            omega
          have h_dvd_sum : p ∣ (n - k) + (k - j) := by rwa [← h_eq]
          have hsub : p ∣ k - j := (Nat.dvd_add_right hdiv_nk).mp h_dvd_sum
          have hpos : 0 < k - j := Nat.sub_pos_of_lt hj
          have h_lt : k - j < p := by omega
          have hle_p : p ≤ k - j := Nat.le_of_dvd hpos hsub
          omega
        have h_not_dvd_desc : ¬ p ∣ n.descFactorial k := by
          rw [Nat.descFactorial_eq_prod_range]
          apply nat_prime_not_dvd_finset_prod hp
          intro x hx; exact h_no_other x (Finset.mem_range.mp hx)
        have h_cop_base : Nat.Coprime p (n.descFactorial k) :=
          hp.coprime_iff_not_dvd.mpr h_not_dvd_desc
        have h_cop : Nat.Coprime (p ^ l) (n.descFactorial k) := by
          rw [Nat.coprime_pow_left_iff hlp]; exact h_cop_base
        exact ⟨k, by omega, h_cop.dvd_of_dvd_mul_right hp_l_dvd⟩
      · -- Case 2: p ∤ n−k. Coprime, push through to n.descFactorial k, apply IH.
        have h_cop_nk : Nat.Coprime p (n - k) := hp.coprime_iff_not_dvd.mpr hdiv_nk
        have h_cop_nk_pow : Nat.Coprime (p ^ l) (n - k) := by
          rw [Nat.coprime_pow_left_iff hlp]; exact h_cop_nk
        rw [mul_comm] at hp_l_dvd
        have h_dvd_desc : p ^ l ∣ n.descFactorial k :=
          h_cop_nk_pow.dvd_of_dvd_mul_right hp_l_dvd
        -- ih: (k < p) → (k ≤ n) → (p^l ∣ n.descFactorial k) → ∃ i < k, p^l ∣ n - i
        rcases ih (by omega) (by omega) h_dvd_desc with ⟨i, hi, h_i_pow⟩
        exact ⟨i, by omega, h_i_pow⟩

/-- Step 1: C(n,k) = m^l, k ≥ 4, n ≥ 2k, l ≥ 2 ⇒ n > k².
Sylvester gives p > k dividing C(n,k). Since C(n,k) = m^l,
p^l | C(n,k). Using n.descFactorial k = k! * C(n,k), we get
p^l | n(n−1)…(n−k+1). By the concentration lemma,
p^l | n−i for some i < k, so n ≥ p^l > k^l ≥ k². -/
lemma erdos_step1_n_gt_k_sq {n k l m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (hl : 2 ≤ l)
    (h_eq : n.choose k = m ^ l) : k * k < n := by
  have hk_pos : 0 < k := by omega
  have hk_le_n : k ≤ n := by omega
  obtain ⟨p, hkp, hp, hp_choose⟩ := sylvester_general n k hn hk_pos
  have hk_lt_p : k < p := hkp
  -- C(n,k) = m^l → p | m → p^l | C(n,k)
  have hp_m : p ∣ m := hp.dvd_of_dvd_pow (h_eq ▸ hp_choose)
  have hp_l_dvd_choose : p ^ l ∣ n.choose k := by
    rw [h_eq]; exact pow_dvd_pow_of_dvd hp_m l
  -- n.descFactorial k = k! * n.choose k, so p^l | n.descFactorial k
  have hp_l_dvd_desc : p ^ l ∣ n.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose n k]
    -- p^l | n.choose k, and n.choose k | k! * n.choose k → transitivity
    -- p^l | n.choose k, and n.choose k | k! * n.choose k
    apply hp_l_dvd_choose.trans
    rw [mul_comm]
    exact dvd_mul_right _ _
  have hl_pos : 0 < l := by omega
  obtain ⟨i, hi, h_i_pow⟩ :=
    pow_l_dvd_one_factor_of_descFactorial hp hk_lt_p hl_pos hk_le_n hp_l_dvd_desc
  have h_n_minus_i_pos : 0 < n - i := Nat.sub_pos_of_lt (by omega)
  have h_ge : p ^ l ≤ n - i := Nat.le_of_dvd h_n_minus_i_pos h_i_pow
  have h_k_l_lt_p_l : k ^ l < p ^ l :=
    Nat.pow_lt_pow_left hk_lt_p (by omega : l ≠ 0)
  have h_k_sq_le_k_l : k * k ≤ k ^ l := by
    calc
      k * k = k ^ 2 := by ring
      _ ≤ k ^ l := Nat.pow_le_pow_right (by omega) hl
  omega



/-! ### Step 2: l-th-power-free decomposition -/





open scoped BigOperators in
lemma self_eq_lPowerFreePart_mul_lPowerRoot_pow (l m : ℕ) (hm : m ≠ 0) :
    m = lPowerFreePart l m * (lPowerRoot l m) ^ l := by
  have h_prod := (Nat.prod_factorization_pow_eq_self hm).symm
  have h_factor (p : ℕ) : p ^ (m.factorization p % l + l * (m.factorization p / l)) =
      (p ^ (m.factorization p % l)) * ((p ^ (m.factorization p / l)) ^ l) := by
    calc
      p ^ (m.factorization p % l + l * (m.factorization p / l))
          = p ^ (m.factorization p % l) * p ^ (l * (m.factorization p / l)) := by rw [pow_add]
      _ = p ^ (m.factorization p % l) * (p ^ (m.factorization p / l)) ^ l := by
        rw [mul_comm l (m.factorization p / l), ← pow_mul]
      _ = (p ^ (m.factorization p % l)) * ((p ^ (m.factorization p / l)) ^ l) := rfl
  dsimp [lPowerFreePart, lPowerRoot]
  calc
    m = m.factorization.prod (· ^ ·) := h_prod
    _ = ∏ p ∈ m.factorization.support, p ^ (m.factorization p) := rfl
    _ = ∏ p ∈ m.factorization.support, p ^ (m.factorization p % l + l * (m.factorization p / l)) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.mod_add_div (m.factorization p) l]
    _ = ∏ p ∈ m.factorization.support,
        (p ^ (m.factorization p % l)) * ((p ^ (m.factorization p / l)) ^ l) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [h_factor p]
    _ = (∏ p ∈ m.factorization.support, p ^ (m.factorization p % l)) *
        (∏ p ∈ m.factorization.support, (p ^ (m.factorization p / l)) ^ l) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ m.factorization.support, p ^ (m.factorization p % l)) *
        (∏ p ∈ m.factorization.support, p ^ (m.factorization p / l)) ^ l := by
      rw [Finset.prod_pow]
    _ = lPowerFreePart l m * (lPowerRoot l m) ^ l := rfl

/-! ### 2-power-free part: factorization mod 2 (Tier 2 building block for Ch03) -/























/-- `lPowerRoot 2` is positive on positive input. -/
theorem lPowerRoot_pos {m : ℕ} (hm : m ≠ 0) :
    0 < lPowerRoot 2 m := by
  by_contra h
  push Not at h
  have h0 : lPowerRoot 2 m = 0 := Nat.le_zero.mp h
  have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 m hm
  rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hsplit
  exact hm hsplit


/-- The 2-power-free part `lPowerFreePart 2 m` divides the squarefree radical
`∏ q ∈ m.primeFactors, q` (since each prime appears with exponent in `{0, 1}`). -/
private lemma lPowerFreePart_dvd_radical (m : ℕ) :
    lPowerFreePart 2 m ∣ ∏ q ∈ m.factorization.support, q := by
  classical
  dsimp [lPowerFreePart]
  refine Finset.prod_dvd_prod_of_dvd _ _ (fun q hq => ?_)
  -- q^(m.factorization q % 2) ∣ q since the exponent is ≤ 1.
  have h_le : m.factorization q % 2 ≤ 1 := by omega
  calc q ^ (m.factorization q % 2)
      ∣ q ^ 1 := pow_dvd_pow q h_le
    _ = q := pow_one q

/-- The 2-power-free part of `m` is squarefree. -/
private lemma lPowerFreePart_squarefree (m : ℕ) (_hm : m ≠ 0) :
    Squarefree (lPowerFreePart 2 m) := by
  classical
  -- The radical ∏ q ∈ supp, q is squarefree, and lPowerFreePart divides it.
  have h_radical_ne : (∏ q ∈ m.factorization.support, q) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors
      ((Nat.support_factorization _).symm ▸ hq)
    exact hq_prime.pos.ne'
  have h_radical_sf : Squarefree (∏ q ∈ m.factorization.support, q) := by
    refine (Nat.squarefree_iff_factorization_le_one h_radical_ne).mpr (fun p => ?_)
    rw [Nat.factorization_prod_apply (fun q hq => by
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors
        ((Nat.support_factorization _).symm ▸ hq)
      exact hq_prime.pos.ne')]
    by_cases hp : p.Prime
    · -- Sum has at most one term equal to 1 (when q = p), rest are 0.
      calc ∑ q ∈ m.factorization.support, q.factorization p
          ≤ ∑ q ∈ m.factorization.support, if q = p then 1 else 0 := by
            refine Finset.sum_le_sum (fun q hq => ?_)
            have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors
              ((Nat.support_factorization _).symm ▸ hq)
            rw [Nat.Prime.factorization hq_prime, Finsupp.single_apply]
        _ = (if p ∈ m.factorization.support then 1 else 0) := by
            rw [Finset.sum_ite_eq']
        _ ≤ 1 := by split_ifs <;> simp
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  -- lPowerFreePart 2 m ∣ radical; divisors of squarefree are squarefree.
  exact h_radical_sf.squarefree_of_dvd (lPowerFreePart_dvd_radical m)

/-- `lPowerFreePart 2` is positive on positive input. -/
theorem lPowerFreePart_pos {m : ℕ} (hm : m ≠ 0) :
    0 < lPowerFreePart 2 m :=
  Nat.pos_of_ne_zero (lPowerFreePart_squarefree m hm).ne_zero

/-- 4 is not squarefree (4 = 2² has factorization {2 ↦ 2}, exceeding the
squarefree bound). -/
theorem not_squarefree_four : ¬ Squarefree (4 : ℕ) := by
  intro hsf
  have h := (Nat.squarefree_iff_factorization_le_one (by norm_num : (4 : ℕ) ≠ 0)).mp hsf 2
  have h4 : (4 : ℕ).factorization 2 = 2 := by
    have : (4 : ℕ) = 2^2 := by norm_num
    rw [this, Nat.factorization_pow_self Nat.prime_two]
  omega

/-- The 2-power-free part of any nonzero natural is never equal to 4 — because
`lPowerFreePart 2 m` is squarefree but 4 is not. This is the obstruction used in
Erdős's `h_l2_contra` step (since `{a_j} = {1, ..., k}` would require `4 ∈ {a_j}`
for `k ≥ 4`). -/
theorem lPowerFreePart_two_ne_four (m : ℕ) (hm : m ≠ 0) :
    lPowerFreePart 2 m ≠ 4 := by
  intro h
  have h_sf := lPowerFreePart_squarefree m hm
  rw [h] at h_sf
  exact not_squarefree_four h_sf




/-- For `m ≠ 0`, the factorization of `lPowerFreePart 2 m` at `p` equals
`m.factorization p % 2`. This is the key arithmetic identity used in the Erdős
divisibility step. -/
private lemma lPowerFreePart_factorization_eq_mod (m p : ℕ) (hm : m ≠ 0) :
    (lPowerFreePart 2 m).factorization p = m.factorization p % 2 := by
  -- m = lPowerFreePart 2 m * (lPowerRoot 2 m)^2, and lPowerFreePart is squarefree.
  have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 m hm
  have hpf_ne : lPowerFreePart 2 m ≠ 0 := by
    intro hz; rw [hz, zero_mul] at hsplit; exact hm hsplit
  have hpr_ne : lPowerRoot 2 m ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hsplit
    exact hm hsplit
  have hfactor :
      m.factorization p = (lPowerFreePart 2 m).factorization p +
        2 * (lPowerRoot 2 m).factorization p := by
    conv_lhs => rw [hsplit]
    rw [Nat.factorization_mul hpf_ne (pow_ne_zero 2 hpr_ne),
        Nat.factorization_pow]
    simp [Finsupp.add_apply, two_mul, Finsupp.smul_apply, smul_eq_mul]
  -- Squarefree ⇒ factorization ≤ 1.
  have h_sf := lPowerFreePart_squarefree m hm
  have h_le : (lPowerFreePart 2 m).factorization p ≤ 1 :=
    Squarefree.natFactorization_le_one p h_sf
  omega





private lemma four_mul_sq_sub_add_two_gt_sq {k : ℕ} (hk : 4 ≤ k) :
    k * k < 4 * (k * k - k + 2) := by
  have h_no_trunc : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
  zify [h_no_trunc]
  have hk_z : (4 : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith only [sq_nonneg ((k : ℤ) - 2), hk_z]

private lemma two_mul_le_succ_sq_sub_sq (b : ℕ) :
    2 * b ≤ (b + 1) ^ 2 - b ^ 2 := by
  have hsq : (b + 1) ^ 2 - b ^ 2 = 2 * b + 1 := by
    ring_nf
    rw [Nat.add_sub_cancel]
  rw [hsq]
  omega

private lemma four_mul_l2_component_le_sq {a b : ℕ} (ha : 0 < a) :
    4 * (a * b ^ 2) ≤ (2 * a * b) * (2 * a * b) := by
  calc
    4 * (a * b ^ 2) ≤ a * (4 * (a * b ^ 2)) :=
      Nat.le_mul_of_pos_left _ ha
    _ = (2 * a * b) * (2 * a * b) := by ring

private lemma lPowerFreePart_l2_ne_of_lt
    {n k m i j : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n)
    (h_eq : n.choose k = m ^ 2) (hi : i ∈ Finset.range k) (hj : j ∈ Finset.range k)
    (hij : i < j) :
    lPowerFreePart 2 (n - i) ≠ lPowerFreePart 2 (n - j) := by
  intro hsame
  have hn_gt : k * k < n := erdos_step1_n_gt_k_sq hk hn (by norm_num) h_eq
  have hi_lt : i < k := Finset.mem_range.mp hi
  have hj_lt : j < k := Finset.mem_range.mp hj
  have hk_le_n : k ≤ n := by omega
  have hi_le_n : i ≤ n := (le_of_lt hi_lt).trans hk_le_n
  have hj_le_n : j ≤ n := (le_of_lt hj_lt).trans hk_le_n
  have hni_ne : n - i ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt (hi_lt.trans_le hk_le_n))
  have hnj_ne : n - j ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt (hj_lt.trans_le hk_le_n))
  have hnj_lt_hni : n - j < n - i := by omega
  have hdiff_nat : j - i = (n - i) - (n - j) := by omega
  have hdiff_lt_k : j - i < k := (Nat.sub_le j i).trans_lt hj_lt
  have hnj_lower : k * k - k + 2 ≤ n - j := by
    apply Nat.le_sub_of_add_le
    have hk_le_kk : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
    have hleft : k * k - k + 2 + j ≤ k * k + 1 := by
      zify [hk_le_kk]
      omega
    exact hleft.trans (Nat.succ_le_of_lt hn_gt)
  set a : ℕ := lPowerFreePart 2 (n - j) with ha_def
  set bi : ℕ := lPowerRoot 2 (n - i) with hbi_def
  set bj : ℕ := lPowerRoot 2 (n - j) with hbj_def
  have ha_pos : 0 < a := by
    rw [ha_def]
    exact lPowerFreePart_pos hnj_ne
  have hbj_pos : 0 < bj := by
    rw [hbj_def]
    exact lPowerRoot_pos hnj_ne
  have hdeci : n - i = a * bi ^ 2 := by
    have h := self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 (n - i) hni_ne
    rw [hsame] at h
    simpa [a, bi, ha_def, hbi_def] using h
  have hdecj : n - j = a * bj ^ 2 := by
    have h := self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 (n - j) hnj_ne
    simpa [a, bj, ha_def, hbj_def] using h
  have hlt_ab : a * bj ^ 2 < a * bi ^ 2 := by
    rw [← hdecj, ← hdeci]
    exact hnj_lt_hni
  have hbj_lt_bi : bj < bi := by
    have hsq : bj * bj < bi * bi := by
      have hsq' : bj ^ 2 < bi ^ 2 := Nat.lt_of_mul_lt_mul_left hlt_ab
      simpa [pow_two] using hsq'
    exact Nat.mul_self_lt_mul_self_iff.mp hsq
  have hbj_succ_sq_le : (bj + 1) ^ 2 ≤ bi ^ 2 := by
    exact Nat.pow_le_pow_left (Nat.succ_le_of_lt hbj_lt_bi) 2
  have hdiff_eq : j - i = a * (bi ^ 2 - bj ^ 2) := by
    calc
      j - i = (n - i) - (n - j) := hdiff_nat
      _ = a * bi ^ 2 - a * bj ^ 2 := by rw [hdeci, hdecj]
      _ = a * (bi ^ 2 - bj ^ 2) := by rw [Nat.mul_sub_left_distrib]
  have hL_le_diff : 2 * a * bj ≤ j - i := by
    rw [hdiff_eq]
    calc
      2 * a * bj = a * (2 * bj) := by ring
      _ ≤ a * ((bj + 1) ^ 2 - bj ^ 2) :=
        Nat.mul_le_mul_left a (two_mul_le_succ_sq_sub_sq bj)
      _ ≤ a * (bi ^ 2 - bj ^ 2) :=
        Nat.mul_le_mul_left a (Nat.sub_le_sub_right hbj_succ_sq_le _)
  have hk_sq_lt_four_nj : k * k < 4 * (n - j) := by
    exact (four_mul_sq_sub_add_two_gt_sq hk).trans_le
      (Nat.mul_le_mul_left 4 hnj_lower)
  have hL_sq_ge : 4 * (n - j) ≤ (2 * a * bj) * (2 * a * bj) := by
    rw [hdecj]
    exact four_mul_l2_component_le_sq ha_pos
  have hk_lt_L : k < 2 * a * bj := by
    exact Nat.mul_self_lt_mul_self_iff.mp (hk_sq_lt_four_nj.trans_le hL_sq_ge)
  exact (not_lt_of_ge hL_le_diff) (hdiff_lt_k.trans hk_lt_L)

/-- Step 3a for the square case: the 2-power-free parts in the descending
factorial are pairwise distinct. -/
theorem lPowerFreePart_injective_l2
    {n k m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (h_eq : n.choose k = m ^ 2) :
    Set.InjOn (fun j => lPowerFreePart 2 (n - j)) (Finset.range k) := by
  intro i hi j hj hsame
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact lPowerFreePart_l2_ne_of_lt hk hn h_eq hi hj hij hsame
  · exact lPowerFreePart_l2_ne_of_lt hk hn h_eq hj hi hji hsame.symm









private lemma strictMono_fin_nat_succ_le {k : ℕ} {f : Fin k → ℕ}
    (hf : StrictMono f) (hpos : ∀ i, 0 < f i) :
    ∀ i, i.1 + 1 ≤ f i := by
  induction k with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ k ih =>
      intro i
      refine Fin.cases ?hzero ?hsucc i
      · exact hpos 0
      · intro i
        have hf_prefix : StrictMono (fun t : Fin k => f (Fin.castSucc t)) := by
          intro a b hab
          exact hf (by simpa using hab)
        have hpos_prefix : ∀ t : Fin k, 0 < f (Fin.castSucc t) :=
          fun t => hpos (Fin.castSucc t)
        have hprev : i.1 + 1 ≤ f (Fin.castSucc i) :=
          ih hf_prefix hpos_prefix i
        have hstep : f (Fin.castSucc i) < f i.succ :=
          hf (Fin.castSucc_lt_succ (i := i))
        have hval : (i.succ : Fin (k + 1)).1 = i.1 + 1 := rfl
        omega

private lemma prod_fin_succ_eq_factorial (k : ℕ) :
    (∏ i : Fin k, ((i : ℕ) + 1)) = k.factorial := by
  calc
    (∏ i : Fin k, ((i : ℕ) + 1)) = ∏ i ∈ Finset.range k, (i + 1) := by
      simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 1) k)
    _ = k.factorial := Finset.prod_range_add_one_eq_factorial k

private lemma prod_orderEmbOfFin_eq {s : Finset ℕ} {k : ℕ} (hcard : s.card = k) :
    (∏ i : Fin k, s.orderEmbOfFin hcard i) = ∏ x ∈ s, x := by
  calc
    (∏ i : Fin k, s.orderEmbOfFin hcard i) =
        ∏ x ∈ Finset.map (s.orderEmbOfFin hcard).toEmbedding Finset.univ, x := by
      simpa using (Finset.prod_map (s := Finset.univ)
        (e := (s.orderEmbOfFin hcard).toEmbedding) (f := fun x : ℕ => x)).symm
    _ = ∏ x ∈ s, x := by
      rw [Finset.map_orderEmbOfFin_univ s hcard]

private lemma factorial_lt_prod_of_card_eq_pos_not_mem_four
    {s : Finset ℕ} {k : ℕ} (hk : 4 ≤ k) (hcard : s.card = k)
    (hpos : ∀ x ∈ s, 0 < x) (h4 : 4 ∉ s) :
    k.factorial < ∏ x ∈ s, x := by
  classical
  let f := s.orderEmbOfFin hcard
  have hf_pos : ∀ i : Fin k, 0 < f i :=
    fun i => hpos (f i) (Finset.orderEmbOfFin_mem s hcard i)
  have hpoint : ∀ i : Fin k, (i : ℕ) + 1 ≤ f i :=
    strictMono_fin_nat_succ_le (f := fun i : Fin k => f i) f.strictMono hf_pos
  let i4 : Fin k := ⟨3, by omega⟩
  have hi4_mem : f i4 ∈ s := Finset.orderEmbOfFin_mem s hcard i4
  have hi4_ne : f i4 ≠ 4 := fun h => h4 (h ▸ hi4_mem)
  have hi4_strict : ((i4 : ℕ) + 1) < f i4 := by
    have hfour_le : 4 ≤ f i4 := by
      simpa [i4] using hpoint i4
    simpa [i4] using lt_of_le_of_ne hfour_le hi4_ne.symm
  have hprod_lt : (∏ i : Fin k, ((i : ℕ) + 1)) < ∏ i : Fin k, f i := by
    exact Finset.prod_lt_prod (fun i _ => by omega) (fun i _ => hpoint i)
      ⟨i4, Finset.mem_univ i4, hi4_strict⟩
  calc
    k.factorial = (∏ i : Fin k, ((i : ℕ) + 1)) :=
      (prod_fin_succ_eq_factorial k).symm
    _ < ∏ i : Fin k, f i := hprod_lt
    _ = ∏ x ∈ s, x := prod_orderEmbOfFin_eq hcard























/-! ### Interval count + Legendre / `padicValNat_factorial` helpers (Tier 2 building blocks for Ch03) -/

/-- Count of `j ∈ range k` with `p ∣ (n - j)`, given `k ≤ n`, is at most `k / p + 1`.
The proof bijects the filter onto multiples of `p` in `Ioc (n - k) n`, then bounds
that count via `Nat.Ioc_filter_dvd_card_eq_div`. -/
private lemma card_filter_dvd_le_aux {n k p : ℕ} (hp : 1 ≤ p) (hkn : k ≤ n) :
    ((Finset.range k).filter (fun j => p ∣ (n - j))).card ≤ k / p + 1 := by
  classical
  -- Step 1: bijection j ↦ n - j onto multiples of p in (n - k, n].
  have h_card_eq :
      ((Finset.range k).filter (fun j => p ∣ (n - j))).card =
        ((Finset.Ioc (n - k) n).filter (fun x => p ∣ x)).card := by
    refine Finset.card_bij (fun j _ => n - j) ?h_mem ?h_inj ?h_surj
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hjk, hjd⟩ := hj
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, hjd⟩ <;> omega
    · intro j1 hj1 j2 hj2 h_eq
      simp only [Finset.mem_filter, Finset.mem_range] at hj1 hj2
      obtain ⟨hj1k, _⟩ := hj1
      obtain ⟨hj2k, _⟩ := hj2
      simp only at h_eq
      omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
      obtain ⟨⟨hx1, hx2⟩, hxd⟩ := hx
      refine ⟨n - x, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have hnn : n - (n - x) = x := by omega
        rw [hnn]; exact hxd
      · simp only
        omega
  rw [h_card_eq]
  -- Step 2: count in (n-k, n] = count in (0, n] - count in (0, n-k] (when k > 0).
  by_cases hk0 : k = 0
  · subst hk0; simp
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
  have h_split : Finset.Ioc 0 n =
      (Finset.Ioc 0 (n - k)) ∪ (Finset.Ioc (n - k) n) := by
    rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega : n - k ≤ n)]
  have h_disj : Disjoint (Finset.Ioc 0 (n - k)) (Finset.Ioc (n - k) n) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Ioc] at hx1 hx2
    omega
  have h_filter_union :
      (Finset.Ioc 0 n).filter (fun x => p ∣ x) =
        (Finset.Ioc 0 (n - k)).filter (fun x => p ∣ x) ∪
          (Finset.Ioc (n - k) n).filter (fun x => p ∣ x) := by
    rw [h_split, Finset.filter_union]
  have h_filter_disj :
      Disjoint ((Finset.Ioc 0 (n - k)).filter (fun x => p ∣ x))
               ((Finset.Ioc (n - k) n).filter (fun x => p ∣ x)) :=
    h_disj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h_card_total :
      ((Finset.Ioc 0 n).filter (fun x => p ∣ x)).card =
        ((Finset.Ioc 0 (n - k)).filter (fun x => p ∣ x)).card +
          ((Finset.Ioc (n - k) n).filter (fun x => p ∣ x)).card := by
    rw [h_filter_union, Finset.card_union_of_disjoint h_filter_disj]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at h_card_total
  -- Step 3: arithmetic — n/p - (n-k)/p ≤ k/p + 1.
  have hp_pos : 0 < p := hp
  have h_split_div : (n - k + k) / p ≤ (n - k) / p + k / p + 1 := by
    have h := Nat.add_div hp_pos (a := n - k) (b := k)
    -- Nat.add_div: (a + b) / n = a/n + b/n + if (a%n + b%n) < n then 0 else 1
    split_ifs at h <;> omega
  have h_sum_eq : (n - k) + k = n := by omega
  rw [h_sum_eq] at h_split_div
  omega

/-! ### Legendre / `padicValNat_factorial` helpers -/



/-- For prime `p` with `p ^ 2 ≤ k`, `(k !).factorization p ≥ k / p + 1`. -/
private lemma factorization_factorial_ge_div_succ
    (k p : ℕ) (hp : p.Prime) (hpk : p ^ 2 ≤ k) :
    k / p + 1 ≤ (k !).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp]
  have hp_pos : 0 < p := hp.pos
  have h_p2_pos : 0 < p ^ 2 := pow_pos hp_pos 2
  have hk_pos : 1 ≤ k := le_trans h_p2_pos hpk
  have hkp : p ≤ k := le_trans (Nat.le_self_pow (by norm_num) p) hpk
  have h_log_ge_two : 2 ≤ Nat.log p k := by
    have := Nat.log_mono_right (b := p) hpk
    rwa [Nat.log_pow hp.one_lt] at this
  have hlog : Nat.log p k < Nat.log p k + 1 := Nat.lt_succ_self _
  rw [padicValNat_factorial hlog]
  have h_split : Finset.Ico 1 (Nat.log p k + 1) =
      insert 1 (Finset.Ico 2 (Nat.log p k + 1)) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [h_split, Finset.sum_insert (by simp [Finset.mem_Ico]), pow_one]
  have h_2_mem : 2 ∈ Finset.Ico 2 (Nat.log p k + 1) := by
    refine Finset.mem_Ico.mpr ⟨le_refl _, ?_⟩
    omega
  have h_p2_div : 1 ≤ k / p ^ 2 := (Nat.one_le_div_iff h_p2_pos).mpr hpk
  have h_rest_ge : 1 ≤ ∑ i ∈ Finset.Ico 2 (Nat.log p k + 1), k / p ^ i := by
    calc 1 ≤ k / p ^ 2 := h_p2_div
      _ ≤ ∑ i ∈ Finset.Ico 2 (Nat.log p k + 1), k / p ^ i :=
          Finset.single_le_sum (f := fun i => k / p ^ i)
            (fun _ _ => Nat.zero_le _) h_2_mem
  omega

/-- For prime `p` with `k < p ^ 2`, Legendre simplifies: `(k !).factorization p = k / p`. -/
private lemma factorization_factorial_eq_div_of_sq_lt
    (k p : ℕ) (hp : p.Prime) (hpk : k < p ^ 2) :
    (k !).factorization p = k / p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp]
  by_cases hk : k = 0
  · subst hk; simp
  have hlog : Nat.log p k < 2 := by
    rw [Nat.log_lt_iff_lt_pow hp.one_lt hk]
    exact hpk
  rw [padicValNat_factorial hlog]
  rw [show (Finset.Ico 1 2 : Finset ℕ) = {1} from rfl, Finset.sum_singleton, pow_one]







/-! ### Erdős divisibility step (general l) -/



/-! ### Erdős divisibility step (l = 2 case): discharge of `hprod_l2` -/

/-- **Erdős divisibility step** (Tier 2 helper).  When `C(n, k)` is a perfect square
with `k ≥ 4` and `n ≥ 2k`, the product of the 2-power-free parts of the descending
factorial `n (n-1) ⋯ (n-k+1)` divides `k !`.

This discharges the `hprod_l2` hypothesis in `chapter03_erdos` for the `l = 2` case. -/
theorem prod_lPowerFreeParts_dvd_factorial_l2
    {n k m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (h_eq : n.choose k = m ^ 2) :
    (∏ j ∈ Finset.range k, lPowerFreePart 2 (n - j)) ∣ k ! := by
  classical
  set P : ℕ := ∏ j ∈ Finset.range k, lPowerFreePart 2 (n - j) with hP_def
  have h_njne : ∀ j ∈ Finset.range k, (n - j) ≠ 0 := fun j hj => by
    have : j < k := Finset.mem_range.mp hj; omega
  have h_factor_ne : ∀ j ∈ Finset.range k, lPowerFreePart 2 (n - j) ≠ 0 := by
    intro j hj hz
    have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 (n - j) (h_njne j hj)
    rw [hz, zero_mul] at hsplit
    exact h_njne j hj hsplit
  have hP_ne : P ≠ 0 := by
    rw [hP_def, Finset.prod_ne_zero_iff]; exact h_factor_ne
  have hkfact_ne : (k ! : ℕ) ≠ 0 := Nat.factorial_ne_zero k
  rw [← Nat.factorization_le_iff_dvd hP_ne hkfact_ne, Finsupp.le_def]
  intro p
  by_cases hp_prime : p.Prime
  · have hp_pos : 1 ≤ p := hp_prime.one_lt.le
    -- P.factorization p = ∑ j ∈ range k, (n - j).factorization p % 2.
    have hP_factor :
        P.factorization p =
          ∑ j ∈ Finset.range k, (n - j).factorization p % 2 := by
      rw [hP_def, Nat.factorization_prod_apply h_factor_ne]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      exact lPowerFreePart_factorization_eq_mod (n - j) p (h_njne j hj)
    -- Upper bound: factorization(P) p ≤ #{j : p ∣ (n-j)} ≤ k/p + 1.
    have h_upper : P.factorization p ≤ k / p + 1 := by
      rw [hP_factor]
      have h_sum_le :
          ∑ j ∈ Finset.range k, (n - j).factorization p % 2 ≤
            ((Finset.range k).filter (fun j => p ∣ (n - j))).card := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range k)
              (fun j => p ∣ (n - j))]
        have h_not_zero :
            ∀ j ∈ ((Finset.range k).filter (fun j => ¬ p ∣ (n - j))),
              (n - j).factorization p % 2 = 0 := by
          intro j hj
          rw [Finset.mem_filter] at hj
          rw [Nat.factorization_eq_zero_of_not_dvd hj.2]
        rw [Finset.sum_congr rfl h_not_zero, Finset.sum_const_zero, add_zero]
        calc
          ∑ j ∈ ((Finset.range k).filter (fun j => p ∣ (n - j))),
              (n - j).factorization p % 2
              ≤ ∑ _ ∈ ((Finset.range k).filter (fun j => p ∣ (n - j))), 1 := by
                refine Finset.sum_le_sum ?_
                intro j _
                have := Nat.mod_lt ((n - j).factorization p) (by norm_num : 0 < 2)
                omega
            _ = ((Finset.range k).filter (fun j => p ∣ (n - j))).card := by
                rw [Finset.sum_const, smul_eq_mul, mul_one]
      have h_card_le := card_filter_dvd_le_aux hp_pos (by omega : k ≤ n)
      omega
    -- Parity: factorization(P) p ≡ factorization(k!) p (mod 2)
    -- from n.descFactorial k = P * Q^2 = k! * m^2.
    have h_parity : P.factorization p % 2 = (k !).factorization p % 2 := by
      set Q : ℕ := ∏ j ∈ Finset.range k, lPowerRoot 2 (n - j) with hQ_def
      have h_desc_split : n.descFactorial k = P * Q ^ 2 := by
        rw [hP_def, hQ_def, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
            Nat.descFactorial_eq_prod_range]
        refine Finset.prod_congr rfl (fun j hj => ?_)
        exact self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 (n - j) (h_njne j hj)
      have h_desc_choose : n.descFactorial k = k ! * m ^ 2 := by
        rw [Nat.descFactorial_eq_factorial_mul_choose, h_eq]
      have hQ_ne : Q ≠ 0 := by
        rw [hQ_def, Finset.prod_ne_zero_iff]
        intro j hj hz
        have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 (n - j) (h_njne j hj)
        rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hsplit
        exact h_njne j hj hsplit
      have h_choose_pos : 0 < n.choose k := Nat.choose_pos (by omega : k ≤ n)
      have hm_ne : m ≠ 0 := by
        intro hz
        rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h_eq
        omega
      have h_eq_PQ : P * Q ^ 2 = k ! * m ^ 2 := by
        rw [show P * Q^2 = n.descFactorial k from h_desc_split.symm]
        exact h_desc_choose
      have h_apply : (P * Q ^ 2).factorization p = (k ! * m ^ 2).factorization p :=
        congrArg (fun n => n.factorization p) h_eq_PQ
      rw [Nat.factorization_mul hP_ne (pow_ne_zero 2 hQ_ne),
          Nat.factorization_mul hkfact_ne (pow_ne_zero 2 hm_ne),
          Nat.factorization_pow, Nat.factorization_pow] at h_apply
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h_apply
      omega
    -- Combine bounds + parity to conclude factorization(P) p ≤ factorization(k!) p.
    by_cases hp_sq : p ^ 2 ≤ k
    · have h_lower := factorization_factorial_ge_div_succ k p hp_prime hp_sq
      omega
    · push Not at hp_sq
      have h_eq_k := factorization_factorial_eq_div_of_sq_lt k p hp_prime hp_sq
      omega
  · -- Non-prime p: both factorizations 0.
    rw [Nat.factorization_eq_zero_of_not_prime _ hp_prime,
        Nat.factorization_eq_zero_of_not_prime _ hp_prime]





/-! ### Main theorem assembly -/




end Tier1

end ProofsInTheBook.Chapter03

open Nat
open ProofsInTheBook.Chapter03

theorem solution
    {n k m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) :
    n.choose k ≠ m ^ 2 := by
  classical
  intro h_eq
  let a : ℕ → ℕ := fun j => lPowerFreePart 2 (n - j)
  let S : Finset ℕ := (Finset.range k).image a
  have hinj : Set.InjOn a (Finset.range k) := by
    simpa [a] using lPowerFreePart_injective_l2 hk hn h_eq
  have hcard : S.card = k := by
    dsimp [S]
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    have hj_lt : j < k := Finset.mem_range.mp hj
    have hnj_ne : n - j ≠ 0 := by
      have hk_le_n : k ≤ n := by omega
      exact Nat.ne_of_gt (Nat.sub_pos_of_lt (hj_lt.trans_le hk_le_n))
    exact lPowerFreePart_pos hnj_ne
  have hprod_S :
      (∏ x ∈ S, x) = ∏ j ∈ Finset.range k, a j := by
    dsimp [S]
    rw [Finset.prod_image hinj]
  have hprod_dvd : (∏ x ∈ S, x) ∣ k ! := by
    rw [hprod_S]
    simpa [a] using prod_lPowerFreeParts_dvd_factorial_l2 hk hn h_eq
  have hprod_pos : 0 < ∏ x ∈ S, x := Finset.prod_pos hpos
  have hfour_mem : 4 ∈ S := by
    by_contra hfour_not
    have hlt : k.factorial < ∏ x ∈ S, x :=
      factorial_lt_prod_of_card_eq_pos_not_mem_four hk hcard hpos hfour_not
    have hle : ∏ x ∈ S, x ≤ k ! :=
      Nat.le_of_dvd (Nat.factorial_pos k) hprod_dvd
    exact (not_lt_of_ge hle) hlt
  rcases Finset.mem_image.mp hfour_mem with ⟨j, hj, hj_eq⟩
  have hj_lt : j < k := Finset.mem_range.mp hj
  have hnj_ne : n - j ≠ 0 := by
    have hk_le_n : k ≤ n := by omega
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt (hj_lt.trans_le hk_le_n))
  exact lPowerFreePart_two_ne_four (n - j) hnj_ne hj_eq
