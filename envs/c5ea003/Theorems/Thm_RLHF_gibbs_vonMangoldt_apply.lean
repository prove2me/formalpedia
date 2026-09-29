-- Prove2me | Theorems.Thm_RLHF_gibbs_vonMangoldt_apply
-- name    : RLHF.gibbs_vonMangoldt_apply
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:47:08.19908+00:00
-- url     : https://prove2.me/theorems/abe86f77-b696-421c-a42c-542a1796cd29
-- title:
--   Closed form of the aligned policy for the von Mangoldt reward.
-- statement:
--   Closed form of the aligned policy for the von Mangoldt reward.
--
--   ```lean
--   theorem RLHF.gibbs_vonMangoldt_apply{β : ℝ} {N : ℕ} (hN : 0 < N) (i : Fin N) :
--       haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
--       gibbsPolicy β (vonMangoldtReward N) (unifRef N) i
--         = vmWeight β N i / ∑ j : Fin N, vmWeight β N j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFPrimeDiscovery.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFPrimeDiscovery.lean#L39

-- Thm stub generated from NumberTheory/RLHFPrimeDiscovery.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
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

theorem RLHF.gibbs_vonMangoldt_apply{β : ℝ} {N : ℕ} (hN : 0 < N) (i : Fin N) :
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
    gibbsPolicy β (vonMangoldtReward N) (unifRef N) i
      = vmWeight β N i / ∑ j : Fin N, vmWeight β N j := by sorry
