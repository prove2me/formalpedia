-- Prove2me | Theorems.Thm_PowerSumReveal_coprime_powerSum_iff_lambda_dvd
-- name    : PowerSumReveal.coprime_powerSum_iff_lambda_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:36:59.427198+00:00
-- url     : https://prove2.me/theorems/384f3974-c259-4655-963d-a983740daf3b
-- title:
--   General Carmichael periodicity.
-- statement:
--   **General Carmichael periodicity.**  For squarefree `N > 0` and `k ≥ 1`, the power sum
--   is coprime to `N` exactly when `λ(N) ∣ k`.
--
--   ```lean
--   theorem PowerSumReveal.coprime_powerSum_iff_lambda_dvd{N k : ℕ} (hN : Squarefree N) (hN0 : N ≠ 0)
--       (hk : k ≠ 0) :
--       Nat.Coprime (powerSum N k) N ↔ lambdaSqfree N ∣ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PowerSumSquarefree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PowerSumSquarefree.lean#L61

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

theorem PowerSumReveal.coprime_powerSum_iff_lambda_dvd{N k : ℕ} (hN : Squarefree N) (hN0 : N ≠ 0)
    (hk : k ≠ 0) :
    Nat.Coprime (powerSum N k) N ↔ lambdaSqfree N ∣ k := by sorry
