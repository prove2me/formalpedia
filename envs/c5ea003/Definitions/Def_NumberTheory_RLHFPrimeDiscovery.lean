-- Prove2me | Definitions.Def_NumberTheory_RLHFPrimeDiscovery
-- name    : NumberTheory_RLHFPrimeDiscovery
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:07.76321+00:00
-- url     : https://prove2.me/theorems/6964dfab-9181-442c-b4f9-b5e83d925b8e
-- title:
--   Aether Catalog definitions — NumberTheory_RLHFPrimeDiscovery
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.RLHFPrimeDiscovery`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/RLHFPrimeDiscovery.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum

/-!
# Reward hacking finds the primes: a quantitative low-temperature theorem

Take the response space `{1, …, N}`, the uniform SFT reference, and the von Mangoldt
reward `Λ`.  The aligned (Gibbs) policy then has the explicit arithmetic form

`π_β(n) ∝ e^{Λ(n)/β} = p^{1/β}` if `n = p^k` is a prime power, and `∝ 1` otherwise.

**Main theorem** (`RLHF.prime_discovery`): as soon as the KL coefficient satisfies
`β log N ≤ log 2`, the aligned policy emits a **prime power** with probability at least
`1/2`.  In other words, a neurosymbolic reward built from the von Mangoldt function
provably drives the aligned model onto the primes once the KL leash is short enough — a
quantitative form of "reward hacking discovers arithmetic structure".

Supporting results: `RLHF.gibbs_vonMangoldt_apply` (closed form of the aligned policy),
`RLHF.sum_nonPrimePow_weight_le` (the non-prime-power mass is at most `N`), and
`RLHF.two_weight_ge` (the response `2` alone already carries weight `≥ N`).
-/

namespace RLHF

open Finset ArithmeticFunction

/-- The subset of responses that are prime powers. -/
def primePowerResponses (N : ℕ) : Finset (Fin N) :=
  univ.filter (fun i => IsPrimePow ((i : ℕ) + 1))

/-- Unnormalized Gibbs weight of a response under the von Mangoldt reward. -/
noncomputable def vmWeight (β : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  Real.exp (Λ ((i : ℕ) + 1) / β)







end RLHF


