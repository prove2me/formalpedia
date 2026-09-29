-- Prove2me | Theorems.Thm_Combinatorics_PowerSumReveal_gcd_powerSum_eq_one_iff
-- name    : Combinatorics.PowerSumReveal.gcd_powerSum_eq_one_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T23:52:33.523713+00:00
-- url     : https://prove2.me/theorems/520255de-6c64-4c23-9a85-29c57739e67e
-- title:
--   Carmichael detection.
-- statement:
--   **Carmichael detection.**  For squarefree `N > 1` and `k ≥ 1`, the gcd is trivial exactly
--   when `k` is a multiple of `λ(N)`.
--
--   ```lean
--   theorem PowerSumReveal.gcd_powerSum_eq_one_iff{N k : ℕ} (hN : 1 < N) (hsq : Squarefree N) (hk : k ≠ 0) :
--       Nat.gcd (powerSum N k) N = 1 ↔ lam N ∣ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/PowerSumFactorReveal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/PowerSumFactorReveal.lean#L246

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

theorem Combinatorics.PowerSumReveal.gcd_powerSum_eq_one_iff{N k : ℕ} (hN : 1 < N) (hsq : Squarefree N) (hk : k ≠ 0) :
    Nat.gcd (powerSum N k) N = 1 ↔ lam N ∣ k := by sorry
