-- Prove2me | solution 1 for RLHF.freeEnergy_ge_point
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:55:28.732177+00:00
-- url     : https://prove2.me/submissions/a5756aed-e729-44d8-8327-55cf0c2f59e1

-- Sol generated from NumberTheory/RLHFTemperatureLimits.lean
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



/-! ## 2. The zero-temperature (greedy) limit -/







/-! ## 3. The high-temperature (reference) limit -/



/-! ## 4. Arithmetic endpoint: the largest prime below `N` -/





open RLHF in
omit [Nonempty Ω] in
theorem solution{β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p) (y : Ω) :
    r y + β * Real.log (p y) ≤ freeEnergy β r p := by
  have hterm : p y * Real.exp (r y / β) ≤ partition β r p := by
    refine Finset.single_le_sum (f := fun w => p w * Real.exp (r w / β)) ?_ (mem_univ y)
    intro w _
    have := (hp.1 w).le
    positivity
  have hpos : 0 < p y * Real.exp (r y / β) := by
    have := hp.1 y; positivity
  have hlog : Real.log (p y * Real.exp (r y / β)) ≤ Real.log (partition β r p) :=
    Real.log_le_log hpos hterm
  rw [Real.log_mul (ne_of_gt (hp.1 y)) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hβ.le
  have hexpand : β * (Real.log (p y) + r y / β) = β * Real.log (p y) + r y := by
    field_simp
  unfold freeEnergy
  linarith [hexpand ▸ hmul]
