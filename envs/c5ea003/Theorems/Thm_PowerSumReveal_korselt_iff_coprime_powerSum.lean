-- Prove2me | Theorems.Thm_PowerSumReveal_korselt_iff_coprime_powerSum
-- name    : PowerSumReveal.korselt_iff_coprime_powerSum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:37:49.137733+00:00
-- url     : https://prove2.me/theorems/b72845b3-c8a3-4bb0-9067-f27ad3b34f78
-- title:
--   Korselt bridge.
-- statement:
--   **Korselt bridge.**  A squarefree `N ≥ 2` satisfies Korselt's criterion — the
--   condition defining Carmichael numbers, `(p-1) ∣ (N-1)` for every prime `p ∣ N` — if and
--   only if the power-sum gcd at exponent `N - 1` is trivial.  Equivalently, Carmichael
--   numbers are exactly the squarefree moduli that defeat the reveal at `k = N-1`.
--
--   ```lean
--   theorem PowerSumReveal.korselt_iff_coprime_powerSum{N : ℕ} (hN : Squarefree N) (hN2 : 2 ≤ N) :
--       (∀ p ∈ N.primeFactors, (p - 1) ∣ (N - 1)) ↔
--         Nat.gcd (powerSum N (N - 1)) N = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PowerSumSquarefree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PowerSumSquarefree.lean#L101

-- Thm stub generated from Geometry/PowerSumSquarefree.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumSquarefree

/-!
# The power-sum reveal for arbitrary squarefree moduli, and a Giuga/Korselt bridge

The semiprime analysis of `Geometry.PowerSumFactorReveal` uses nothing about the
number of prime factors: for **any** squarefree `N` and any prime `p ∣ N`,

`p ∣ powerSum N k ↔ ¬ (p - 1) ∣ k`   (`k ≥ 1`).

Consequently `gcd (powerSum N k) N = 1` exactly when `λ(N) ∣ k`, where
`λ(N) = lcm_{p ∣ N} (p - 1)` is the Carmichael function of a squarefree number.
This is the general form of the "Carmichael periodicity" phenomenon.

The last section links this to two classical topics.

* *Fermat/Giuga.*  For a prime `p`, `powerSum p (p-1) ≡ -1 (mod p)`.
* *Korselt.*  A squarefree `N` is a Korselt number (`(p-1) ∣ (N-1)` for all `p ∣ N`,
  the criterion defining Carmichael numbers) **iff** the power-sum gcd at the natural
  exponent `k = N - 1` is trivial.  So Carmichael numbers are precisely the squarefree
  moduli on which the exponent `N-1` gives the method no information.

## Main results

* `PowerSumReveal.prime_dvd_powerSum_iff_squarefree`
* `PowerSumReveal.coprime_powerSum_iff_lambda_dvd`
* `PowerSumReveal.powerSum_prime_eq_neg_one` (Fermat/Giuga direction)
* `PowerSumReveal.korselt_iff_coprime_powerSum`
-/

open PowerSumReveal

open Finset

theorem PowerSumReveal.korselt_iff_coprime_powerSum{N : ℕ} (hN : Squarefree N) (hN2 : 2 ≤ N) :
    (∀ p ∈ N.primeFactors, (p - 1) ∣ (N - 1)) ↔
      Nat.gcd (powerSum N (N - 1)) N = 1 := by sorry
