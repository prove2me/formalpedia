-- Prove2me | Definitions.Def_Combinatorics_PowerSumPolynomialBarrier
-- name    : Combinatorics_PowerSumPolynomialBarrier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:45:26.685101+00:00
-- url     : https://prove2.me/theorems/f9a0ec17-c296-4f2a-b7ee-fd293e5af224
-- title:
--   Aether Catalog definitions — Combinatorics_PowerSumPolynomialBarrier
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.PowerSumPolynomialBarrier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/PowerSumPolynomialBarrier.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_PowerSumFactorReveal

/-!
# A degree barrier for aggregated-sum factoring

The power-sum reveal of `Combinatorics.PowerSumFactorReveal` first produces a factor of
`N = pq` at the exponent `k = min (p-1, q-1)`.  Is that an artifact of using *monomials*
`a ↦ a^k` as the aggregation weights?  This file shows that it is not: **no** integer
polynomial of degree below `min (p-1, q-1)` can reveal anything.

For `f ∈ ℤ[X]` put `S_f(N) = ∑_{a=1}^{N} f(a)` (`polySum`).  The key local computation
(`cast_polySum`, a strict generalisation of `cast_powerSum`) is

`S_f(N) ≡ (N/p) · ∑_{x ∈ ZMod p} f̄(x)  (mod p)`  for every prime `p ∣ N`,

and over `ZMod p` the total sum of a polynomial of degree `< p - 1` vanishes
(`sum_eval_eq_zero_of_natDegree_lt`).  Hence:

* `polySum_dvd_of_natDegree_lt` — `p ∣ S_f(N)` whenever `p ∣ N` and `deg f < p - 1`;
* `polySum_degree_barrier` — for a semiprime `N = pq` and `deg f < min (p-1, q-1)` the whole
  modulus divides `S_f(N)`, so `gcd (S_f(N), N) = N`: **every** low-degree aggregation
  returns no information whatsoever;
* `polySum_barrier_sharp` — the bound is sharp: at degree exactly `p - 1` the monomial
  `X^{p-1}` does reveal a factor.

This turns the informal complexity remark ("first hit at `k* = min(p-1,q-1) ≈ √N`") into a
theorem about an entire family of algorithms rather than one particular weighting.
-/

namespace PowerSumReveal

open Finset Polynomial

/-- `S_f(N) = ∑_{a=1}^{N} f(a)` for an integer polynomial `f`. -/
def polySum (f : Polynomial ℤ) (N : ℕ) : ℤ := ∑ a ∈ Finset.Icc 1 N, f.eval (a : ℤ)









end PowerSumReveal


