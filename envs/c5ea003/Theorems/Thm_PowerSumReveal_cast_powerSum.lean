-- Prove2me | Theorems.Thm_PowerSumReveal_cast_powerSum
-- name    : PowerSumReveal.cast_powerSum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:25:23.271251+00:00
-- url     : https://prove2.me/theorems/0154e6d0-fdc7-47a2-b656-f38e884654c6
-- title:
--   Local formula.
-- statement:
--   **Local formula.**  Modulo a prime divisor `p` of `N`, the power sum collapses to
--   `(N/p) · (if (p-1) ∣ k then -1 else 0)`.
--
--   ```lean
--   theorem PowerSumReveal.cast_powerSum(N p k : ℕ) (hp : p.Prime) (hpN : p ∣ N) (hk : k ≠ 0) :
--       ((powerSum N k : ℕ) : ZMod p) = (N / p) • (if (p - 1) ∣ k then (-1 : ZMod p) else 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/PowerSumFactorReveal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/PowerSumFactorReveal.lean#L94

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

theorem PowerSumReveal.cast_powerSum(N p k : ℕ) (hp : p.Prime) (hpN : p ∣ N) (hk : k ≠ 0) :
    ((powerSum N k : ℕ) : ZMod p) = (N / p) • (if (p - 1) ∣ k then (-1 : ZMod p) else 0) := by sorry
