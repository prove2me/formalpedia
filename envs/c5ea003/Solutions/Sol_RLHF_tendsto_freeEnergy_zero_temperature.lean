-- Prove2me | solution 1 for RLHF.tendsto_freeEnergy_zero_temperature
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:25:07.192233+00:00
-- url     : https://prove2.me/submissions/4c66d2dd-59dc-4b8b-b4dc-8de05e1dd086

-- Sol generated from NumberTheory/RLHFTemperatureLimits.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureLimits
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_freeEnergy_ge_point
import Theorems.Thm_RLHF_freeEnergy_le_of_le

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


theorem le_rewardMax (r : Ω → ℝ) (y : Ω) : r y ≤ rewardMax r :=
  Finset.le_sup' r (mem_univ y)

theorem exists_rewardMax (r : Ω → ℝ) : ∃ y, r y = rewardMax r := by
  obtain ⟨y, _, hy⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := Ω)) r
  exact ⟨y, hy.symm⟩

theorem freeEnergy_le_rewardMax {β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p) :
    freeEnergy β r p ≤ rewardMax r :=
  freeEnergy_le_of_le hβ hp (le_rewardMax r)

/-- Quantitative greedy bound: at low temperature the free energy is within
`β log (1 / p y⋆)` of the maximal reward. -/
theorem rewardMax_sub_le_freeEnergy {β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    {y : Ω} (hy : r y = rewardMax r) :
    rewardMax r + β * Real.log (p y) ≤ freeEnergy β r p := by
  have h := freeEnergy_ge_point (r := r) hβ hp y
  rwa [hy] at h


/-! ## 3. The high-temperature (reference) limit -/



/-! ## 4. Arithmetic endpoint: the largest prime below `N` -/





open RLHF in
theorem solution{r p : Ω → ℝ} (hp : IsPosDist p) :
    Tendsto (fun β => freeEnergy β r p) (𝓝[>] (0 : ℝ)) (𝓝 (rewardMax r)) := by
  obtain ⟨y, hy⟩ := exists_rewardMax r
  have hlow : Tendsto (fun β : ℝ => rewardMax r + β * Real.log (p y)) (𝓝[>] (0 : ℝ))
      (𝓝 (rewardMax r)) := by
    have hc : Tendsto (fun β : ℝ => rewardMax r + β * Real.log (p y)) (𝓝 (0 : ℝ))
        (𝓝 (rewardMax r + 0 * Real.log (p y))) :=
      tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    simp only [zero_mul, add_zero] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact rewardMax_sub_le_freeEnergy hβ hp hy
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact freeEnergy_le_rewardMax hβ hp
