-- Prove2me | Theorems.Thm_PowerSumGCD_exists_pollard_bad_base
-- name    : PowerSumGCD.exists_pollard_bad_base
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:21:19.273221+00:00
-- url     : https://prove2.me/theorems/f227a0ba-5160-4de8-a449-4e13e872585c
-- title:
--   Pollard `p-1` has bad bases.
-- statement:
--   **Pollard `p-1` has bad bases.**  For distinct odd primes `p, q` and any even
--   exponent `M`, there is a base `1 < a < pq` for which `gcd(a^M - 1, pq) = pq`: the
--   method returns the whole modulus and reveals nothing.  The witness is the CRT element
--   `a ≡ 1 (mod p)`, `a ≡ -1 (mod q)`.
--
--   ```lean
--   theorem PowerSumGCD.exists_pollard_bad_base{p q M : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
--       (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hM : Even M) :
--       ∃ a : ℕ, 1 < a ∧ a < p * q ∧ Nat.gcd (a ^ M - 1) (p * q) = p * q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PowerSumGCDRobustness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PowerSumGCDRobustness.lean#L43

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

theorem PowerSumGCD.exists_pollard_bad_base{p q M : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hM : Even M) :
    ∃ a : ℕ, 1 < a ∧ a < p * q ∧ Nat.gcd (a ^ M - 1) (p * q) = p * q := by sorry
