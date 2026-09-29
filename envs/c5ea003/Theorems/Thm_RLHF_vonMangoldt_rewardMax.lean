-- Prove2me | Theorems.Thm_RLHF_vonMangoldt_rewardMax
-- name    : RLHF.vonMangoldt_rewardMax
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:49:50.880035+00:00
-- url     : https://prove2.me/theorems/bfe87b5d-3ef1-4d05-845c-54d09f8a7bef
-- title:
--   For `N ≥ 2` the maximum of the von Mangoldt reward on `{1, …, N}` is `log P`, where `P`
-- statement:
--   For `N ≥ 2` the maximum of the von Mangoldt reward on `{1, …, N}` is `log P`, where `P`
--   is the largest prime `≤ N`.
--
--   ```lean
--   theorem RLHF.vonMangoldt_rewardMax{N : ℕ} (hN : 2 ≤ N) :
--       ∃ P : ℕ, P.Prime ∧ P ≤ N ∧ (∀ q : ℕ, q.Prime → q ≤ N → q ≤ P) ∧
--         haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega : 0 < N)
--         rewardMax (vonMangoldtReward N) = Real.log P := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFTemperatureLimits.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFTemperatureLimits.lean#L216

-- Thm stub generated from NumberTheory/RLHFTemperatureLimits.lean
import Mathlib
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



/-! ## 2. The zero-temperature (greedy) limit -/







/-! ## 3. The high-temperature (reference) limit -/



/-! ## 4. Arithmetic endpoint: the largest prime below `N` -/

theorem RLHF.vonMangoldt_rewardMax{N : ℕ} (hN : 2 ≤ N) :
    ∃ P : ℕ, P.Prime ∧ P ≤ N ∧ (∀ q : ℕ, q.Prime → q ≤ N → q ≤ P) ∧
      haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega : 0 < N)
      rewardMax (vonMangoldtReward N) = Real.log P := by sorry
