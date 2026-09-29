-- Prove2me | solution 1 for PowerSumReveal.cast_powerSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:10:54.873265+00:00
-- url     : https://prove2.me/submissions/f7ebe4bd-f730-4ad0-b693-ba6ae5d19c79

-- Sol generated from Combinatorics/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Combinatorics_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_sum_range_mul_cast

/-!
# Power-sum factor reveal for squarefree moduli

For a modulus `N` let
`F(N, k) = ∑_{a = 1}^{N} a ^ k`  (`PowerSumReveal.powerSum`).

The central observation is a **complete local computation**: if `p` is a prime
dividing `N` and `k ≥ 1`, then modulo `p` the interval `{1, …, N}` covers each
residue class exactly `N / p` times, so

`F(N, k) ≡ (N / p) · ∑_{x ∈ ZMod p} x ^ k ≡ (N / p) · (if (p-1) ∣ k then -1 else 0)  (mod p)`.

For squarefree `N` this gives the exact criterion

`p ∣ F(N, k) ↔ ¬ (p - 1) ∣ k`,

hence the exact evaluation of the gcd

`gcd (F(N, k), N) = ∏ { p ∈ N.primeFactors | ¬ (p - 1) ∣ k }`,

which for a semiprime `N = p q` specialises to
`gcd (F(N, k), N) = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`,
and in particular `gcd (F(N, p-1), N) = q` whenever `(q-1) ∤ (p-1)`.

Main results:

* `sum_pow_zmod` — `∑_{x : ZMod p} x ^ k = if (p-1) ∣ k then -1 else 0` for `k ≠ 0`.
* `cast_powerSum` — the local formula for `F(N,k)` modulo a prime divisor of `N`.
* `prime_dvd_powerSum_iff` — `p ∣ F(N,k) ↔ ¬ (p-1) ∣ k` for squarefree `N`.
* `gcd_powerSum_semiprime` — Theorem 1, in exact (all `k`) form.
* `powerSum_reveal` — the factoring corollary at `k = p - 1`.
* `gcd_powerSum_squarefree` — the general squarefree product formula.
* `gcd_powerSum_eq_one_iff` — the gcd is `1` exactly on multiples of the
  Carmichael function `λ(N) = lcm_{p ∣ N} (p-1)`.
-/

open PowerSumReveal

open Finset

/-! ## The local sum over `ZMod p` -/

/-- **Fermat/Euler power sum.**  For `k ≠ 0` the sum of `k`-th powers over all of
`ZMod p` is `-1` when `(p-1) ∣ k` and `0` otherwise. -/
theorem sum_pow_zmod (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : k ≠ 0) :
    ∑ x : ZMod p, x ^ k = if (p - 1) ∣ k then -1 else 0 := by
  have h1 : ∑ x : (ZMod p)ˣ, ((x : ZMod p)) ^ k
      = if Fintype.card (ZMod p) - 1 ∣ k then -1 else 0 :=
    FiniteField.sum_pow_units (ZMod p) k
  rw [ZMod.card p] at h1
  rw [← h1]
  have h2 : ∑ x : (ZMod p)ˣ, ((x : ZMod p)) ^ k = ∑ x : {y : ZMod p // y ≠ 0}, ((x : ZMod p)) ^ k :=
    Fintype.sum_equiv (unitsEquivNeZero) _ _ (fun _ => rfl)
  rw [h2, ← Finset.sum_subtype (Finset.univ.erase (0 : ZMod p)) (by intro x; simp) (fun x => x ^ k)]
  exact (Finset.sum_erase _ (by simp [hk])).symm



/-- Monomial specialisation of `sum_range_mul_cast`. -/
theorem sum_range_mul_cast_pow (p : ℕ) [NeZero p] (k m : ℕ) :
    ∑ a ∈ range (m * p), ((a : ZMod p)) ^ k = m • (∑ x : ZMod p, x ^ k) :=
  sum_range_mul_cast p (fun x => x ^ k) m

/-! ## The power sum and its local values -/






/-! ## The gcd evaluation -/






/-! ## The general squarefree formula -/





open PowerSumReveal in
theorem solution(N p k : ℕ) (hp : p.Prime) (hpN : p ∣ N) (hk : k ≠ 0) :
    ((powerSum N k : ℕ) : ZMod p) = (N / p) • (if (p - 1) ∣ k then (-1 : ZMod p) else 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast : ((powerSum N k : ℕ) : ZMod p) = ∑ a ∈ Finset.Icc 1 N, ((a : ZMod p)) ^ k := by
    simp [powerSum]
  have hins : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext x; simp [Finset.mem_Icc]; omega
  have h1 : ∑ a ∈ Finset.range (N + 1), ((a : ZMod p)) ^ k
      = ∑ a ∈ Finset.Icc 1 N, ((a : ZMod p)) ^ k := by
    rw [hins, Finset.sum_insert (by simp)]
    simp [hk]
  have h2 : ∑ a ∈ Finset.range (N + 1), ((a : ZMod p)) ^ k
      = ∑ a ∈ Finset.range N, ((a : ZMod p)) ^ k := by
    rw [Finset.sum_range_succ, (ZMod.natCast_eq_zero_iff N p).mpr hpN]
    simp [hk]
  have hN : N = (N / p) * p := (Nat.div_mul_cancel hpN).symm
  rw [hcast, ← h1, h2, show (Finset.range N) = Finset.range ((N / p) * p) by rw [← hN],
    sum_range_mul_cast_pow p k (N / p), sum_pow_zmod p hk]
