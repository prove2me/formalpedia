-- Prove2me | solution 1 for PowerSumGCD.pow_even_modEq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:25:31.068378+00:00
-- url     : https://prove2.me/submissions/8d083605-bff9-46cb-900a-ccc363f2028e

-- Sol generated from Novelty/PowerSumGCDRobustness.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring

/-!
# Robustness: the power sum has no "bad base", Pollard `p-1` always does

Pollard's `p-1` method computes `gcd(a^M - 1, N)` for a chosen base `a` and a smooth
exponent `M`.  The method *fails* (returns `N`, i.e. no information) whenever the chosen
base happens to satisfy `a^M ≡ 1` modulo **both** prime factors.

Here we show that for any product of two distinct odd primes and any even exponent `M`
such a bad base always exists — it is the CRT element `a ≡ 1 (mod p)`, `a ≡ -1 (mod q)` —
whereas the power sum `F(N,k) = ∑_{a=1}^{N} a^k` involves no base at all: it aggregates
every residue simultaneously, and by `gcd_powerSum_eq_factor` it produces the factor `q`
at `k = p-1` unconditionally (given `(q-1) ∤ (p-1)`).

## Main results

* `pow_even_modEq_one` : `s^M ≡ 1 (mod s+1)` for even `M` (the `(-1)^even = 1` mechanism);
* `exists_pollard_bad_base` : for distinct odd primes `p, q` and even `M > 0` there is a
  base `1 < a < pq` with `gcd(a^M - 1, pq) = pq`, i.e. Pollard's step fails;
* `powerSum_robust_vs_pollard` : at the very exponent `M = p-1` where the power sum
  hands over the factor `q`, a bad Pollard base exists.
-/

open PowerSumGCD





open PowerSumGCD in
theorem solution{s M : ℕ} (hs : 1 ≤ s) (hM : Even M) : s ^ M ≡ 1 [MOD s + 1] := by
  obtain ⟨t, rfl⟩ := hM
  have hsq : s ^ 2 ≡ 1 [MOD s + 1] := by
    obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
    have hdvd : (u + 1 + 1) ∣ (u + 1) ^ 2 - 1 := by
      refine ⟨u, ?_⟩
      have h1 : (u + 1) ^ 2 = u * u + 2 * u + 1 := by ring
      have h2 : (u + 1 + 1) * u = u * u + 2 * u := by ring
      omega
    exact ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr hdvd).symm
  have hpow : s ^ (t + t) = (s ^ 2) ^ t := by
    rw [← pow_mul]
    ring_nf
  rw [hpow]
  simpa using hsq.pow t
