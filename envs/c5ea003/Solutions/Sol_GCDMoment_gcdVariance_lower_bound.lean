-- Prove2me | solution 1 for GCDMoment.gcdVariance_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:35:57.558239+00:00
-- url     : https://prove2.me/submissions/d9aed8b6-76ef-466a-be25-f732a7537083

-- Sol generated from Novelty/GCDMomentTraceWitness.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Theorems.Thm_GCDMoment_gcdMoment_ge
import Theorems.Thm_GCDMoment_gcdMoment_le

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



/-- The natural-number form of the upper bound. -/
theorem gcdMoment_le_nat (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (j : ℕ) :
    gcdMoment (j + 1) (p * q) ≤ 4 * (p * q) ^ (j + 1) := by
  have h := gcdMoment_le hp hq hpq j
  have : ((gcdMoment (j + 1) (p * q) : ℕ) : ℤ) ≤ ((4 * (p * q) ^ (j + 1) : ℕ) : ℤ) := by
    push_cast; push_cast at h; linarith
  exact_mod_cast this





/-! ### Witness density -/





open GCDMoment in
theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (j : ℕ) :
    ((p * q : ℕ) : ℚ) ^ (2 * j + 1) - 16 * ((p * q : ℕ) : ℚ) ^ (2 * j)
      ≤ gcdVariance (j + 1) (p * q) := by
  have hNpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hN : (0 : ℚ) < ((p * q : ℕ) : ℚ) := by exact_mod_cast hNpos
  have h1 : ((p * q : ℕ) : ℚ) ^ (2 * j + 2) ≤ (gcdMoment (2 * (j + 1)) (p * q) : ℚ) := by
    have h := gcdMoment_ge (2 * (j + 1)) (p * q) hNpos
    have h' : (((p * q) ^ (2 * (j + 1)) : ℕ) : ℚ) ≤ (gcdMoment (2 * (j + 1)) (p * q) : ℚ) := by
      exact_mod_cast h
    calc ((p * q : ℕ) : ℚ) ^ (2 * j + 2) = (((p * q) ^ (2 * (j + 1)) : ℕ) : ℚ) := by
          push_cast; ring_nf
      _ ≤ _ := h'
  have h2 : (gcdMoment (j + 1) (p * q) : ℚ) ≤ 4 * ((p * q : ℕ) : ℚ) ^ (j + 1) := by
    have h := gcdMoment_le_nat hp hq hpq j
    have h' : ((gcdMoment (j + 1) (p * q) : ℕ) : ℚ) ≤ ((4 * (p * q) ^ (j + 1) : ℕ) : ℚ) := by
      exact_mod_cast h
    calc (gcdMoment (j + 1) (p * q) : ℚ) ≤ ((4 * (p * q) ^ (j + 1) : ℕ) : ℚ) := h'
      _ = 4 * ((p * q : ℕ) : ℚ) ^ (j + 1) := by push_cast; ring
  unfold gcdVariance
  have e1 : ((p * q : ℕ) : ℚ) ^ (2 * j + 1)
      ≤ (gcdMoment (2 * (j + 1)) (p * q) : ℚ) / ((p * q : ℕ) : ℚ) := by
    rw [le_div_iff₀ hN]
    calc ((p * q : ℕ) : ℚ) ^ (2 * j + 1) * ((p * q : ℕ) : ℚ)
        = ((p * q : ℕ) : ℚ) ^ (2 * j + 2) := by ring
      _ ≤ _ := h1
  have e2 : ((gcdMoment (j + 1) (p * q) : ℚ) / ((p * q : ℕ) : ℚ)) ^ 2
      ≤ 16 * ((p * q : ℕ) : ℚ) ^ (2 * j) := by
    have hdiv : (gcdMoment (j + 1) (p * q) : ℚ) / ((p * q : ℕ) : ℚ)
        ≤ 4 * ((p * q : ℕ) : ℚ) ^ j := by
      rw [div_le_iff₀ hN]
      calc (gcdMoment (j + 1) (p * q) : ℚ) ≤ 4 * ((p * q : ℕ) : ℚ) ^ (j + 1) := h2
        _ = 4 * ((p * q : ℕ) : ℚ) ^ j * ((p * q : ℕ) : ℚ) := by ring
    have hnn : (0 : ℚ) ≤ (gcdMoment (j + 1) (p * q) : ℚ) / ((p * q : ℕ) : ℚ) := by positivity
    calc ((gcdMoment (j + 1) (p * q) : ℚ) / ((p * q : ℕ) : ℚ)) ^ 2
        ≤ (4 * ((p * q : ℕ) : ℚ) ^ j) ^ 2 := by nlinarith
      _ = 16 * ((p * q : ℕ) : ℚ) ^ (2 * j) := by rw [mul_pow, ← pow_mul]; ring_nf
  linarith
