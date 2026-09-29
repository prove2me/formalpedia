-- Prove2me | Theorems.Thm_PowerSumReveal_cast_polySum
-- name    : PowerSumReveal.cast_polySum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:27:24.746238+00:00
-- url     : https://prove2.me/theorems/8a1b22ed-2d02-4457-be5a-a0339e7da92b
-- title:
--   Local formula for a general aggregation polynomial.
-- statement:
--   **Local formula for a general aggregation polynomial.**  For a prime `p ∣ N`,
--   `S_f(N) ≡ (N/p) · ∑_{x ∈ ZMod p} f̄(x)` modulo `p`.
--
--   ```lean
--   theorem PowerSumReveal.cast_polySum(N p : ℕ) [Fact p.Prime] (hpN : p ∣ N) (f : Polynomial ℤ) :
--       ((polySum f N : ℤ) : ZMod p)
--         = (N / p) • ∑ x : ZMod p, (f.map (Int.castRingHom (ZMod p))).eval x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/PowerSumPolynomialBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/PowerSumPolynomialBarrier.lean#L47

-- Thm stub generated from Combinatorics/PowerSumPolynomialBarrier.lean
import Mathlib
import Definitions.Def_Combinatorics_PowerSumFactorReveal
import Definitions.Def_Combinatorics_PowerSumPolynomialBarrier

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

open PowerSumReveal

open Finset Polynomial

theorem PowerSumReveal.cast_polySum(N p : ℕ) [Fact p.Prime] (hpN : p ∣ N) (f : Polynomial ℤ) :
    ((polySum f N : ℤ) : ZMod p)
      = (N / p) • ∑ x : ZMod p, (f.map (Int.castRingHom (ZMod p))).eval x := by sorry
