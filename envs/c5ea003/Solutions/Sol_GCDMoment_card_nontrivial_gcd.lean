-- Prove2me | solution 1 for GCDMoment.card_nontrivial_gcd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:09:30.77754+00:00
-- url     : https://prove2.me/submissions/6b3f8599-7c35-445c-a96a-dc62d51abb90

-- Sol generated from Novelty/GCDMomentTraceWitness.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentTraceWitness

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
theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    #{x ∈ Finset.range (p * q) | (p * q).gcd x ≠ 1} = p + q - 1 := by
  classical
  have hcard := Finset.card_filter_add_card_filter_not
    (s := Finset.range (p * q)) (p := fun x => (p * q).gcd x = 1)
  have hphi : φ (p * q) = #{x ∈ Finset.range (p * q) | (p * q).gcd x = 1} := rfl
  have htot : φ (p * q) = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hpq), Nat.totient_prime hp,
      Nat.totient_prime hq]
  rw [Finset.card_range, ← hphi, htot] at hcard
  have h2p := hp.two_le
  have h2q := hq.two_le
  have hexp : (p - 1) * (q - 1) + p + q - 1 = p * q := by
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 2 := ⟨p - 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 2 := ⟨q - 2, by omega⟩
    have e1 : (a + 2 - 1) * (b + 2 - 1) = a * b + a + b + 1 := by
      rw [show a + 2 - 1 = a + 1 from rfl, show b + 2 - 1 = b + 1 from rfl]; ring
    have e2 : (a + 2) * (b + 2) = a * b + 2 * a + 2 * b + 4 := by ring
    omega
  have hne : #{x ∈ Finset.range (p * q) | ¬((p * q).gcd x = 1)}
      = #{x ∈ Finset.range (p * q) | (p * q).gcd x ≠ 1} := rfl
  rw [hne] at hcard
  omega
