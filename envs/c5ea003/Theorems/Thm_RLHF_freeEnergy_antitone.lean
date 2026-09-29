-- Prove2me | Theorems.Thm_RLHF_freeEnergy_antitone
-- name    : RLHF.freeEnergy_antitone
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:42:30.926091+00:00
-- url     : https://prove2.me/theorems/0912ef62-e9c8-4da4-9252-8e23737e4b7a
-- title:
--   Monotonicity in the KL temperature.
-- statement:
--   **Monotonicity in the KL temperature.**  A larger KL coefficient can only decrease the
--   optimal value of the RLHF objective.
--
--   ```lean
--   theorem RLHF.freeEnergy_antitone{β₁ β₂ : ℝ} {r p : Ω → ℝ}
--       (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hle : β₁ ≤ β₂) (hp : IsPosDist p) :
--       freeEnergy β₂ r p ≤ freeEnergy β₁ r p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFTemperatureSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFTemperatureSpectrum.lean#L38

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

theorem RLHF.freeEnergy_antitone{β₁ β₂ : ℝ} {r p : Ω → ℝ}
    (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hle : β₁ ≤ β₂) (hp : IsPosDist p) :
    freeEnergy β₂ r p ≤ freeEnergy β₁ r p := by sorry
