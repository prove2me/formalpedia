-- Prove2me | Definitions.Def_Novelty_GCDMomentTraceWitness
-- name    : Novelty_GCDMomentTraceWitness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:26:31.558925+00:00
-- url     : https://prove2.me/theorems/9dcae0d1-d08a-49a4-bdb8-6493599b1d9e
-- title:
--   Aether Catalog definitions — Novelty_GCDMomentTraceWitness
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.GCDMomentTraceWitness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/GCDMomentTraceWitness.lean by skeleton subtraction
import Mathlib

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

namespace GCDMoment

open Finset Nat

/-! ### Definition and the divisor form -/

/-- `gcdMoment k n = ∑_{x < n} gcd(n,x)^k`, the `k`-th gcd moment of `n`. -/
def gcdMoment (k n : ℕ) : ℕ := ∑ x ∈ Finset.range n, (n.gcd x) ^ k





/-! ### Newton power sums and the moment polynomial -/

/-- The Newton power sums `P_j` as a polynomial recursion in the public data `(N, s)`:
`P_0 = 2`, `P_1 = s`, `P_{j+2} = s P_{j+1} − N P_j`. -/
def newtonP (N s : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => s
  | (j + 2) => s * newtonP N s (j + 1) - N * newtonP N s j



/-- `momentPoly N s k = F_{k+1}(N,s)`, the closed form of the `(k+1)`-st gcd moment. -/
def momentPoly (N s : ℤ) (k : ℕ) : ℤ :=
  N ^ (k + 1) + N * newtonP N s k - newtonP N s (k + 1) + N - s + 1



/-! ### The explicit low moments -/





variable {p q : ℕ}





/-! ### Trace recovery and closure of the family -/



/-! ### The `k = 2` root structure -/




/-! ### The trace splits `N` -/




/-! ### The cost hierarchy: variance of the `k`-th gcd power -/




/-- The variance of `gcd(N, U)^k` for `U` uniform on the residues mod `N`. -/
noncomputable def gcdVariance (k n : ℕ) : ℚ :=
  (gcdMoment (2 * k) n : ℚ) / n - ((gcdMoment k n : ℚ) / n) ^ 2




/-! ### Witness density -/




end GCDMoment


