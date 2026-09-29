-- Prove2me | Theorems.Thm_RLHF_two_weight_ge
-- name    : RLHF.two_weight_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:46:57.358154+00:00
-- url     : https://prove2.me/theorems/29136504-ea25-475c-80fe-4bddb05ec20c
-- title:
--   Under the threshold `β log N ≤ log 2`, the single response `2` already carries Gibbs
-- statement:
--   Under the threshold `β log N ≤ log 2`, the single response `2` already carries Gibbs
--   weight at least `N`.
--
--   ```lean
--   theorem RLHF.two_weight_ge{β : ℝ} {N : ℕ} (hN : 2 ≤ N) (hβ : 0 < β)
--       (hthr : β * Real.log N ≤ Real.log 2) :
--       (N : ℝ) ≤ vmWeight β N ⟨1, by omega⟩ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFPrimeDiscovery.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFPrimeDiscovery.lean#L75

-- Thm stub generated from NumberTheory/RLHFPrimeDiscovery.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFPrimeDiscovery
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

open RLHF

open Finset ArithmeticFunction

theorem RLHF.two_weight_ge{β : ℝ} {N : ℕ} (hN : 2 ≤ N) (hβ : 0 < β)
    (hthr : β * Real.log N ≤ Real.log 2) :
    (N : ℝ) ≤ vmWeight β N ⟨1, by omega⟩ := by sorry
