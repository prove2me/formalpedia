-- Prove2me | Theorems.Thm_RLHF_kl_budget
-- name    : RLHF.kl_budget
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:47:24.184877+00:00
-- url     : https://prove2.me/theorems/54f7925b-bd9c-4f7f-ad7a-6fca9a7f73a7
-- title:
--   No policy collapse.
-- statement:
--   **No policy collapse.**  The KL divergence of the aligned policy from the reference
--   obeys the budget `β · KL ≤ max r − min r`.
--
--   ```lean
--   theorem RLHF.kl_budget{β m M : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
--       (hm : ∀ y, m ≤ r y) (hM : ∀ y, r y ≤ M) :
--       β * klDiv (gibbsPolicy β r p) p ≤ M - m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFTemperatureLimits.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFTemperatureLimits.lean#L52

-- Thm stub generated from NumberTheory/RLHFTemperatureLimits.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureLimits
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum

/-!
# Zero- and infinite-temperature limits of the RLHF free energy

Continuing `NumberTheory.RLHFTemperatureSpectrum`, we quantify the two endpoints of the
free-energy spectrum `V(β) = β log Z(β)`:

* `RLHF.kl_budget` — the aligned policy cannot collapse: `β · KL(π_β ‖ p) ≤ max r − min r`.
* `RLHF.freeEnergy_ge_point` — `V(β) ≥ r y + β log p y` for every response `y`.
* `RLHF.tendsto_freeEnergy_zero_temperature` — as `β → 0⁺`, `V(β) → max r`
  (greedy reward maximization).
* `RLHF.freeEnergy_le_high_temperature` and `RLHF.tendsto_freeEnergy_high_temperature`
  — as `β → ∞`, `V(β) → 𝔼_p[r]` (the SFT reference), with the explicit rate
  `V(β) ≤ min r + e^{(max r − min r)/β} (𝔼_p[r] − min r)`.

Arithmetic payoff (`RLHF.vonMangoldt_zero_temperature_limit`): for the von Mangoldt reward
on `{1, …, N}` the zero-temperature limit of the RLHF free energy equals `log P` where `P`
is the **largest prime ≤ N**, while the infinite-temperature limit is the Chebyshev average
`ψ(N)/N`.  The whole alignment spectrum of this reward model is thus pinned between two
classical prime-counting quantities.
-/

open RLHF

open Finset ArithmeticFunction Filter Topology

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Pointwise lower bounds and the KL budget -/

theorem RLHF.kl_budget{β m M : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hm : ∀ y, m ≤ r y) (hM : ∀ y, r y ≤ M) :
    β * klDiv (gibbsPolicy β r p) p ≤ M - m := by sorry
