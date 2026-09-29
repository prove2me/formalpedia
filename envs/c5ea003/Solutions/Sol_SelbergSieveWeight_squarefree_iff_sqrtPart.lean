-- Prove2me | solution 1 for SelbergSieveWeight.squarefree_iff_sqrtPart
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:36:53.657415+00:00
-- url     : https://prove2.me/submissions/f3689764-c3ca-48bc-b80e-3ead7cc5faa0

-- Sol generated from Speculative/NumberTheory/SelbergSieveWeight.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_SelbergSieveWeight
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


/-- The `p`-adic valuation of `sqrtPart n` is `⌊v_p(n) / 2⌋`. -/
theorem sqrtPart_fact (n : ℕ) (p : ℕ) :
    (sqrtPart n).factorization p = n.factorization p / 2 := by
  have : (sqrtPart n).factorization = n.factorization.mapRange (· / 2) (Nat.zero_div 2) := by
    apply Nat.prod_pow_factorization_eq_self
    intro q hq
    have h2 : q ∈ n.factorization.support := Finsupp.support_mapRange hq
    rw [Nat.support_factorization] at h2
    exact Nat.prime_of_mem_primeFactors h2
  rw [this, Finsupp.mapRange_apply]

theorem sqrtPart_ne_zero (n : ℕ) : sqrtPart n ≠ 0 := by
  have : 0 < sqrtPart n := by
    apply Nat.prod_pow_pos_of_zero_notMem_support
    intro H
    rw [Finsupp.mem_support_iff, Finsupp.mapRange_apply] at H
    exact H (by simp)
  omega





open SelbergSieveWeight in
theorem solution(n : ℕ) (hne : n ≠ 0) :
    Squarefree n ↔ sqrtPart n = 1 := by
  rw [Nat.squarefree_iff_factorization_le_one hne]
  constructor
  · intro h
    have hz : (sqrtPart n).factorization = 0 := by
      ext p; rw [sqrtPart_fact, Finsupp.coe_zero, Pi.zero_apply]
      have := h p; omega
    rcases (Nat.factorization_eq_zero_iff' (sqrtPart n)).mp hz with h0 | h1
    · exact absurd h0 (sqrtPart_ne_zero n)
    · exact h1
  · intro h p
    have : (sqrtPart n).factorization p = 0 := by rw [h]; simp
    rw [sqrtPart_fact] at this; omega
