-- Prove2me | Theorems.Thm_PowerSumReveal_gcd_powerSum_squarefree
-- name    : PowerSumReveal.gcd_powerSum_squarefree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:25:26.049325+00:00
-- url     : https://prove2.me/theorems/d1ec228c-6f24-4f17-846b-ff2969fd3886
-- title:
--   General reveal theorem.
-- statement:
--   **General reveal theorem.**  For squarefree `N ≥ 1` and `k ≥ 1`,
--   `gcd (F(N,k), N)` is exactly the product of the prime divisors `p` of `N`
--   with `(p-1) ∤ k`.
--
--   ```lean
--   theorem PowerSumReveal.gcd_powerSum_squarefree{N k : ℕ} (hN : N ≠ 0) (hsq : Squarefree N) (hk : k ≠ 0) :
--       Nat.gcd (powerSum N k) N = ∏ p ∈ N.primeFactors.filter (fun p => ¬ (p - 1) ∣ k), p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/PowerSumFactorReveal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/PowerSumFactorReveal.lean#L201

-- Thm stub generated from Combinatorics/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Combinatorics_PowerSumFactorReveal

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





/-! ## The power sum and its local values -/






/-! ## The gcd evaluation -/






/-! ## The general squarefree formula -/

theorem PowerSumReveal.gcd_powerSum_squarefree{N k : ℕ} (hN : N ≠ 0) (hsq : Squarefree N) (hk : k ≠ 0) :
    Nat.gcd (powerSum N k) N = ∏ p ∈ N.primeFactors.filter (fun p => ¬ (p - 1) ∣ k), p := by sorry
