-- Prove2me | solution 1 for PowerSumReveal.cast_polySum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:10:53.982779+00:00
-- url     : https://prove2.me/submissions/02b3320a-1859-42f1-ae3d-eff7d6764638

-- Sol generated from Combinatorics/PowerSumPolynomialBarrier.lean
import Mathlib
import Definitions.Def_Combinatorics_PowerSumFactorReveal
import Definitions.Def_Combinatorics_PowerSumPolynomialBarrier
import Theorems.Thm_PowerSumReveal_sum_range_mul_cast

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



/-- Reduction of an integer polynomial evaluation modulo `p`. -/
theorem cast_eval (p : ℕ) (f : Polynomial ℤ) (a : ℤ) :
    ((f.eval a : ℤ) : ZMod p) = (f.map (Int.castRingHom (ZMod p))).eval ((a : ZMod p)) := by
  rw [Polynomial.eval_map]
  exact (Polynomial.eval₂_at_apply (Int.castRingHom (ZMod p)) a).symm








open PowerSumReveal in
theorem solution(N p : ℕ) [Fact p.Prime] (hpN : p ∣ N) (f : Polynomial ℤ) :
    ((polySum f N : ℤ) : ZMod p)
      = (N / p) • ∑ x : ZMod p, (f.map (Int.castRingHom (ZMod p))).eval x := by
  set g : ZMod p → ZMod p := fun x => (f.map (Int.castRingHom (ZMod p))).eval x with hg
  have hcast : ((polySum f N : ℤ) : ZMod p) = ∑ a ∈ Finset.Icc 1 N, g ((a : ℕ) : ZMod p) := by
    rw [polySum]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [cast_eval p f (a : ℤ)]
    simp [hg]
  have hins : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext x; simp [Finset.mem_Icc]; omega
  have h1 : ∑ a ∈ Finset.range (N + 1), g ((a : ℕ) : ZMod p)
      = g 0 + ∑ a ∈ Finset.Icc 1 N, g ((a : ℕ) : ZMod p) := by
    rw [hins, Finset.sum_insert (by simp)]
    simp
  have hN0 : ((N : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).mpr hpN
  have h2 : ∑ a ∈ Finset.range (N + 1), g ((a : ℕ) : ZMod p)
      = ∑ a ∈ Finset.range N, g ((a : ℕ) : ZMod p) + g 0 := by
    rw [Finset.sum_range_succ, hN0]
  have hN : N = (N / p) * p := (Nat.div_mul_cancel hpN).symm
  have h3 : ∑ a ∈ Finset.Icc 1 N, g ((a : ℕ) : ZMod p)
      = ∑ a ∈ Finset.range N, g ((a : ℕ) : ZMod p) := by
    have := h1.symm.trans h2
    exact add_left_cancel (by rw [this]; ring)
  rw [hcast, h3, show (Finset.range N) = Finset.range ((N / p) * p) by rw [← hN],
    sum_range_mul_cast p g (N / p)]
