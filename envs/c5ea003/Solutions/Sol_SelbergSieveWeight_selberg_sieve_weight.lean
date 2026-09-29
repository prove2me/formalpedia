-- Prove2me | solution 1 for SelbergSieveWeight.selberg_sieve_weight
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:40:02.471339+00:00
-- url     : https://prove2.me/submissions/63caf706-266f-44c0-9e4c-03035ff29a39

-- Sol generated from Speculative/NumberTheory/SelbergSieveWeight.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_SelbergSieveWeight
import Theorems.Thm_SelbergSieveWeight_dvd_sq_iff
import Theorems.Thm_SelbergSieveWeight_squarefree_iff_sqrtPart
/-
# Selberg sieve weight identity

This module proves the combinatorial identity underlying the Selberg sieve weights:
for every positive integer `n`,
$$\mu^2(n) = \sum_{d^2 \mid n} \mu(d),$$
where `μ` is the Möbius function.

The proof proceeds by introducing the *square-root part* `sqrtPart n`, the largest
integer `m` such that `m^2 ∣ n` (equivalently the number whose `p`-adic valuation is
`⌊v_p(n)/2⌋`).  The key observations are:

* `d ^ 2 ∣ n ↔ d ∣ sqrtPart n` (`dvd_sq_iff`), so the divisors `d` with `d^2 ∣ n`
  are exactly the divisors of `sqrtPart n`;
* `∑_{d ∣ m} μ(d) = if m = 1 then 1 else 0` (Möbius inversion of the constant
  function `1`, via `moebius_mul_coe_zeta`);
* `Squarefree n ↔ sqrtPart n = 1` (`squarefree_iff_sqrtPart`), matching the value of
  `μ^2(n)` given by `moebius_sq`.

Only the definition and basic properties of `μ` and prime factorizations are used; no
results about prime distribution (π(x), Chebyshev bounds, etc.) enter the argument.
-/

open ArithmeticFunction

open SelbergSieveWeight



theorem sqrtPart_ne_zero (n : ℕ) : sqrtPart n ≠ 0 := by
  have : 0 < sqrtPart n := by
    apply Nat.prod_pow_pos_of_zero_notMem_support
    intro H
    rw [Finsupp.mem_support_iff, Finsupp.mapRange_apply] at H
    exact H (by simp)
  omega





open SelbergSieveWeight in
theorem solution(n : ℕ) (hn : 0 < n) :
    (moebius n) ^ 2 = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), moebius d := by
  have hne : n ≠ 0 := hn.ne'
  have hset : n.divisors.filter (fun d => d ^ 2 ∣ n) = (sqrtPart n).divisors := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hd, _⟩, hd2⟩
      have hdne : d ≠ 0 := by rintro rfl; exact hne (by simpa using hd)
      exact ⟨(dvd_sq_iff n d hne hdne).mp hd2, sqrtPart_ne_zero n⟩
    · rintro ⟨hdvd, _⟩
      have hdne : d ≠ 0 := by rintro rfl; exact (sqrtPart_ne_zero n) (zero_dvd_iff.mp hdvd)
      have hd2 := (dvd_sq_iff n d hne hdne).mpr hdvd
      exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num)) hd2, hne⟩, hd2⟩
  rw [hset]
  have hsum : ∑ d ∈ (sqrtPart n).divisors, moebius d = if sqrtPart n = 1 then 1 else 0 := by
    have h2 : (moebius * (ArithmeticFunction.zeta) : ArithmeticFunction ℤ) (sqrtPart n)
        = ∑ d ∈ (sqrtPart n).divisors, moebius d := ArithmeticFunction.coe_mul_zeta_apply
    rw [← h2, ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  rw [hsum, ArithmeticFunction.moebius_sq]
  simp only [squarefree_iff_sqrtPart n hne]
