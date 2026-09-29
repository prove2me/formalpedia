-- Prove2me | solution 1 for GCDMoment.gcdMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:34:10.804901+00:00
-- url     : https://prove2.me/submissions/3bc6fcfb-9353-4538-863a-ab8eebbcda82

-- Sol generated from Novelty/GCDMomentTraceWitness.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Theorems.Thm_GCDMoment_gcdMoment_semiprime_four_terms

/-!
# GCD moments of a semiprime: a closed trace-witness family

For a positive integer `n` and an exponent `k` put

`M_k(n) = ∑_{x < n} gcd(n, x) ^ k`

(the sum over a full residue system; the term `x = 0` contributes `n ^ k`, which is the same
as the term `x = n` in the more usual range `1 ≤ x ≤ n`).

This file develops the arithmetic of these *gcd moments* for a **semiprime** `N = p * q`
(`p`, `q` distinct primes), the setting of the factoring-barrier catalog.  Writing
`s = p + q` for the *trace*, the results are as follows.

## Main results

* `gcdMoment_eq_sum_divisors` — the classical gcd-sum / Jordan-totient identity
  `M_k(n) = ∑_{d ∣ n} d^k φ(n/d)`, valid for every `n > 0`.
* `newtonP_eq` — the Newton recursion `P_{j+2} = s P_{j+1} − N P_j` computes the power sums
  `P_j = p^j + q^j` from the pair `(N, s)` alone.
* `gcdMoment_semiprime_four_terms` and `gcdMoment_eq_momentPoly` — **the closed form**: for
  `k ≥ 1`, `M_k(N) = N^k + N·P_{k−1} − P_k + N − s + 1 = F_k(N, s)`, an explicit integer
  polynomial in the *public* modulus `N` and the trace `s`.  This is the symmetry barrier:
  the individual factors never appear, only their elementary symmetric functions.
* `gcdMoment_one`, `gcdMoment_two`, `gcdMoment_three`, `gcdMoment_four` — the explicit
  low-order polynomials, e.g. `M_1 = 4N − 2s + 1` and `M_2 = N² + 3N + 1 + (N−1)s − s²`.
* `trace_of_gcdMoment_one` — the first moment recovers the trace exactly: `2 s = 4N + 1 − M_1`.
* `higher_moments_from_first` — **closure of the family**: every higher moment is an explicit
  function of `N` and `M_1`.  No moment carries information beyond the trace.
* `sum_prod_determines_pair`, `discriminant_eq` and `factorization_of_gcdMoment_one` — the
  trace *does* split `N`: the pair `(p,q)` is the unique ordered pair of naturals with the
  observed product and trace, and the discriminant `s² − 4N = (q−p)²` is a perfect square.
  So `M_1` is a complete witness — but computing it costs `Θ(N)` gcds.
* `momentPoly_two_symm`, `momentPoly_two_root_dichotomy`, `trace_unique_of_small` — the
  `k = 2` moment polynomial has exactly the two roots `s` and `N − 1 − s`, and the size cut
  `2s < N − 1` picks out the true trace.  (The second root is not a phantom: the companion file
  `Novelty.GCDMomentPairInversion` exhibits moduli where it is realised by a genuine second
  factorisation, and shows there are exactly two such moduli.)
* `gcdMoment_ge`, `gcdMoment_le`, `gcdVariance_lower_bound`, `gcdVariance_upper_bound`,
  `gcdVariance_theta`, `gcdVariance_one_le`, `gcdVariance_separation` — the *cost* hierarchy.  The variance of `gcd(N,U)^k` for uniform
  `U` is at least `N^{2k−1} − 16 N^{2k−2}`, while for `k = 1` it is at most `4N`; hence
  Chebyshev sampling at level `k` needs `Ω(N^{2k−1})` samples and `k = 1` is optimal.
* `card_nontrivial_gcd` — the witness-density law `#{x < N : gcd(N,x) ≠ 1} = p + q − 1`:
  a uniform probe hits a nontrivial gcd with probability exactly `(p+q−1)/N`, the `Θ(p+q)`
  query threshold.

Nothing here breaks the factoring barrier: every statement is either an identity in `(N, s)`
or an `Ω(N)`-cost computation.
-/

open GCDMoment

open Finset Nat

/-! ### Definition and the divisor form -/



/-- Sanity checks against the closed forms below (`N = 6`, `s = 5`; `N = 15`, `s = 8`). -/
example : gcdMoment 1 6 = 15 := by decide
example : gcdMoment 2 6 = 55 := by decide
example : gcdMoment 1 15 = 4 * 15 - 2 * 8 + 1 := by decide




/-! ### Newton power sums and the moment polynomial -/







/-! ### The explicit low moments -/





variable {p q : ℕ}





/-! ### Trace recovery and closure of the family -/



/-! ### The `k = 2` root structure -/




/-! ### The trace splits `N` -/




/-! ### The cost hierarchy: variance of the `k`-th gcd power -/








/-! ### Witness density -/





open GCDMoment in
theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (j : ℕ) :
    (gcdMoment (j + 1) (p * q) : ℤ) ≤ 4 * ((p : ℤ) * q) ^ (j + 1) := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
  have hpN : (p : ℤ) ≤ (p : ℤ) * q := by nlinarith
  have hqN : (q : ℤ) ≤ (p : ℤ) * q := by nlinarith
  have hp0 : (0 : ℤ) ≤ p := by linarith
  have hq0 : (0 : ℤ) ≤ q := by linarith
  have hpj : (p : ℤ) ^ j ≤ ((p : ℤ) * q) ^ j := pow_le_pow_left₀ hp0 hpN j
  have hqj : (q : ℤ) ^ j ≤ ((p : ℤ) * q) ^ j := pow_le_pow_left₀ hq0 hqN j
  have hNj : (0 : ℤ) < ((p : ℤ) * q) ^ j := by positivity
  rw [gcdMoment_semiprime_four_terms hp hq hpq]
  have e1 : (p : ℤ) ^ (j + 1) * ((q : ℤ) - 1) ≤ ((p : ℤ) * q) ^ (j + 1) := by
    have : (p : ℤ) ^ (j + 1) * ((q : ℤ) - 1) ≤ (p : ℤ) ^ j * ((p : ℤ) * q) := by
      rw [pow_succ]; nlinarith [pow_nonneg hp0 j]
    calc (p : ℤ) ^ (j + 1) * ((q : ℤ) - 1) ≤ (p : ℤ) ^ j * ((p : ℤ) * q) := this
      _ ≤ ((p : ℤ) * q) ^ j * ((p : ℤ) * q) := by nlinarith
      _ = ((p : ℤ) * q) ^ (j + 1) := by rw [pow_succ]
  have e2 : (q : ℤ) ^ (j + 1) * ((p : ℤ) - 1) ≤ ((p : ℤ) * q) ^ (j + 1) := by
    have : (q : ℤ) ^ (j + 1) * ((p : ℤ) - 1) ≤ (q : ℤ) ^ j * ((p : ℤ) * q) := by
      rw [pow_succ]; nlinarith [pow_nonneg hq0 j]
    calc (q : ℤ) ^ (j + 1) * ((p : ℤ) - 1) ≤ (q : ℤ) ^ j * ((p : ℤ) * q) := this
      _ ≤ ((p : ℤ) * q) ^ j * ((p : ℤ) * q) := by nlinarith
      _ = ((p : ℤ) * q) ^ (j + 1) := by rw [pow_succ]
  have e3 : ((p : ℤ) - 1) * ((q : ℤ) - 1) ≤ ((p : ℤ) * q) ^ (j + 1) := by
    have h1 : ((p : ℤ) - 1) * ((q : ℤ) - 1) ≤ (p : ℤ) * q := by nlinarith
    have h2 : ((p : ℤ) * q) ≤ ((p : ℤ) * q) ^ (j + 1) := by
      rw [pow_succ]; nlinarith
    linarith
  linarith
