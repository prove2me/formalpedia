-- Prove2me | Theorems.Thm_PowerSumGCD_pow_even_modEq_one
-- name    : PowerSumGCD.pow_even_modEq_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:20:54.425777+00:00
-- url     : https://prove2.me/theorems/73620aac-a160-42d0-958b-19e9c3e6791a
-- title:
--   `s ≡ -1 (mod s+1)`, so every even power of `s` is `1` modulo `s+1`.
-- statement:
--   `s ≡ -1 (mod s+1)`, so every even power of `s` is `1` modulo `s+1`.
--
--   ```lean
--   theorem PowerSumGCD.pow_even_modEq_one{s M : ℕ} (hs : 1 ≤ s) (hM : Even M) : s ^ M ≡ 1 [MOD s + 1] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PowerSumGCDRobustness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PowerSumGCDRobustness.lean#L26

-- Thm stub generated from Novelty/PowerSumGCDRobustness.lean
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

theorem PowerSumGCD.pow_even_modEq_one{s M : ℕ} (hs : 1 ≤ s) (hM : Even M) : s ^ M ≡ 1 [MOD s + 1] := by sorry
