-- Prove2me | solution 1 for PowerSumReveal.sum_eval_eq_zero_of_natDegree_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:13:45.570843+00:00
-- url     : https://prove2.me/submissions/4d001f13-9153-4bec-b57e-ec9a78761483

-- Sol generated from Combinatorics/PowerSumPolynomialBarrier.lean
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











open PowerSumReveal in
theorem solution(p : ℕ) [Fact p.Prime] (F : Polynomial (ZMod p))
    (hdeg : F.natDegree < p - 1) : ∑ x : ZMod p, F.eval x = 0 := by
  have hstep : ∀ x : ZMod p, F.eval x = ∑ i ∈ range (F.natDegree + 1), F.coeff i * x ^ i :=
    fun x => Polynomial.eval_eq_sum_range x
  calc ∑ x : ZMod p, F.eval x
      = ∑ x : ZMod p, ∑ i ∈ range (F.natDegree + 1), F.coeff i * x ^ i := by
        exact Finset.sum_congr rfl (fun x _ => hstep x)
    _ = ∑ i ∈ range (F.natDegree + 1), F.coeff i * ∑ x : ZMod p, x ^ i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm)
    _ = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hilt : i < Fintype.card (ZMod p) - 1 := by
          rw [ZMod.card p]
          have := Finset.mem_range.mp hi
          omega
        rw [FiniteField.sum_pow_lt_card_sub_one (ZMod p) i hilt, mul_zero]
