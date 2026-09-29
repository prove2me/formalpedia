-- Prove2me | solution 1 for RLHF.tendsto_freeEnergy_high_temperature
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:25:06.68726+00:00
-- url     : https://prove2.me/submissions/b3a6c527-73a1-4b7e-9e8b-e9e6e4377b80

-- Sol generated from NumberTheory/RLHFTemperatureLimits.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureLimits
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_freeEnergy_ge_reference
import Theorems.Thm_RLHF_freeEnergy_le_high_temperature

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





open RLHF in
theorem solution{m M : ℝ} {r p : Ω → ℝ} (hp : IsPosDist p)
    (hm : ∀ y, m ≤ r y) (hM : ∀ y, r y ≤ M) :
    Tendsto (fun β => freeEnergy β r p) atTop (𝓝 (∑ y, p y * r y)) := by
  set E := ∑ y, p y * r y with hE
  have hdiv : Tendsto (fun β : ℝ => (M - m) / β) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hexp : Tendsto (fun β : ℝ => Real.exp ((M - m) / β)) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp hdiv
    simpa using this
  have hup : Tendsto (fun β : ℝ => m + Real.exp ((M - m) / β) * (E - m)) atTop (𝓝 E) := by
    have h : Tendsto (fun β : ℝ => m + Real.exp ((M - m) / β) * (E - m)) atTop
        (𝓝 (m + 1 * (E - m))) :=
      Filter.Tendsto.add tendsto_const_nhds (hexp.mul tendsto_const_nhds)
    have heq : m + 1 * (E - m) = E := by ring
    rwa [heq] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact freeEnergy_ge_reference hβ hp
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact freeEnergy_le_high_temperature hβ hp hm hM
