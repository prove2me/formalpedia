-- Prove2me | Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
-- name    : NumberTheory_RLHFTemperatureSpectrum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:11.051983+00:00
-- url     : https://prove2.me/theorems/f911f6d1-914f-4f95-86ab-b7aab039e584
-- title:
--   Aether Catalog definitions — NumberTheory_RLHFTemperatureSpectrum
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.RLHFTemperatureSpectrum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/RLHFTemperatureSpectrum.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational

/-!
# The RLHF free-energy spectrum and a von Mangoldt reward model

Building on `NumberTheory.RLHFGibbsVariational`, we study the *free energy*
`V(β) = β log Z(β)`, which by the Gibbs variational principle is the optimal value of
the KL-regularized RLHF objective at temperature `β`.

Main results:

* `RLHF.freeEnergy_antitone` — `V` is antitone in the KL coefficient `β`:
  stronger regularization can only lower the achievable value.
* `RLHF.freeEnergy_le_of_le` — `V(β) ≤ sup r` (no reward hacking beyond the reward ceiling).
* `RLHF.freeEnergy_ge_reference` — `V(β) ≥ 𝔼_p[r]` (RLHF never hurts).
* `RLHF.gibbs_ne_reference_of_nonconstant` and `RLHF.strict_improvement` — RLHF strictly
  improves on the SFT reference exactly when the reward model is non-constant.
* Number-theoretic instantiation: reward `r(n) = Λ(n)` (von Mangoldt) on the response
  space `{1, …, N}` with the uniform SFT reference.  Then the free energy is squeezed,
  `ψ(N)/N ≤ V(β) ≤ log N` (`RLHF.vonMangoldt_freeEnergy_ge_chebyshev`,
  `RLHF.vonMangoldt_freeEnergy_le_log`), and for `N ≥ 2` the lower bound is *strict*
  (`RLHF.vonMangoldt_strict_improvement`): the alignment gain is powered exactly by the
  irregularity of the primes.
-/

namespace RLHF

open Finset ArithmeticFunction

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The free energy `V(β) = β log Z(β)`, i.e. the optimal value of the RLHF objective. -/
noncomputable def freeEnergy (β : ℝ) (r p : Ω → ℝ) : ℝ := β * Real.log (partition β r p)







/-! ## The von Mangoldt reward model on `{1, …, N}` -/

/-- The uniform SFT reference policy on `Fin N`. -/
noncomputable def unifRef (N : ℕ) : Fin N → ℝ := fun _ => 1 / (N : ℝ)

/-- The von Mangoldt reward: response `i` (representing the integer `i + 1`) is scored by
`Λ (i+1)`, i.e. `log p` if `i + 1` is a power of the prime `p` and `0` otherwise. -/
noncomputable def vonMangoldtReward (N : ℕ) : Fin N → ℝ := fun i => Λ ((i : ℕ) + 1)

/-- The Chebyshev `ψ`-function restricted to the response space, `ψ(N) = ∑_{n ≤ N} Λ n`. -/
noncomputable def chebyshevPsiFin (N : ℕ) : ℝ := ∑ i : Fin N, Λ ((i : ℕ) + 1)






end RLHF


