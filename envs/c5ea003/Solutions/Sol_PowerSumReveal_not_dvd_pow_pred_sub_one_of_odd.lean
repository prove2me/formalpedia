-- Prove2me | solution 1 for PowerSumReveal.not_dvd_pow_pred_sub_one_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:15.091904+00:00
-- url     : https://prove2.me/submissions/42e53f3f-bf99-480b-be6d-843bb17cb85c

-- Sol generated from Geometry/PowerSumPollardRobustness.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPollardRobustness

/-!
# Robustness: the power sum has no "bad base", Pollard's `p-1` does

Pollard's `p-1` method depends on a *base* `a`: it computes `gcd (a^M - 1, N)` and
succeeds only if the multiplicative order of `a` modulo one prime factor divides the
exponent `M` while the order modulo the other one does not.  The power-sum quantity
`powerSum N k = ∑_{a=1}^{N} a^k` has no base parameter at all: it aggregates every
residue simultaneously.

This file makes the contrast precise.

* `PowerSumReveal.pollard_universally_bad_base` — for a semiprime `N = p*q` of distinct
  *odd* primes, the base `a = N - 1` (a nontrivial base, coprime to `N`) is bad for
  **every** exponent `M ≥ 1`: `gcd (a^M - 1, N) ∈ {1, N}`, never a proper factor.
* `PowerSumReveal.powerSum_succeeds_where_pollard_fails` — at the very exponent
  `k = p - 1` where that base makes Pollard return the useless value `N`, the power
  sum returns the factor `q` (under the standard side condition `(q-1) ∤ (p-1)`).
* `PowerSumReveal.pollard_bad_base_example` — the concrete instance `N = 35`, `M = 4`,
  `a = 6`: Pollard returns `35`, the power sum returns `7`.

Note that the statement `a = N - 1` is a genuinely nontrivial base: `1 < N - 1 < N`.
-/

open PowerSumReveal

open Finset

variable {p q : ℕ}


/-- Casting `(N-1)^M - 1` into `ZMod p`. -/
lemma cast_pow_pred_sub_one (r N M : ℕ) [NeZero r] (hN : 2 ≤ N) :
    (((N - 1) ^ M - 1 : ℕ) : ZMod r) = ((N : ZMod r) - 1) ^ M - 1 := by
  have h1 : 1 ≤ (N - 1) ^ M := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h1]
  push_cast [Nat.cast_sub (show 1 ≤ N by omega)]
  ring








open PowerSumReveal in
theorem solution{r N M : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrN : r ∣ N) (hN : 2 ≤ N) (hM : Odd M) :
    ¬ r ∣ ((N - 1) ^ M - 1) := by
  haveI : Fact r.Prime := ⟨hr⟩
  intro hdvd
  have h0 : (((N - 1) ^ M - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ r).2 hdvd
  rw [cast_pow_pred_sub_one r N M hN, (ZMod.natCast_eq_zero_iff N r).2 hrN, zero_sub,
    hM.neg_one_pow] at h0
  have h2 : ((2 : ℕ) : ZMod r) = 0 := by
    have : (-1 : ZMod r) - 1 = -(2 : ZMod r) := by ring
    rw [this] at h0
    have := neg_eq_zero.mp h0
    exact_mod_cast this
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
    ((ZMod.natCast_eq_zero_iff 2 r).1 h2))
