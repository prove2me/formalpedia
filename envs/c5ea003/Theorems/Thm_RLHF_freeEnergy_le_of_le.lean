-- Prove2me | Theorems.Thm_RLHF_freeEnergy_le_of_le
-- name    : RLHF.freeEnergy_le_of_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:43:37.624496+00:00
-- url     : https://prove2.me/theorems/6ae10c29-2850-472f-88a8-330042f5ec5b
-- title:
--   The optimal value never exceeds the ceiling of the reward model.
-- statement:
--   The optimal value never exceeds the ceiling of the reward model.
--
--   ```lean
--   theorem RLHF.freeEnergy_le_of_le{β M : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
--       (hM : ∀ y, r y ≤ M) : freeEnergy β r p ≤ M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFTemperatureSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFTemperatureSpectrum.lean#L57

-- Thm stub generated from NumberTheory/RLHFTemperatureSpectrum.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum

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

open RLHF

open Finset ArithmeticFunction

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem RLHF.freeEnergy_le_of_le{β M : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hM : ∀ y, r y ≤ M) : freeEnergy β r p ≤ M := by sorry
