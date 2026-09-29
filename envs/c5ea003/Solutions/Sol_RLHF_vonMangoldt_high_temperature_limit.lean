-- Prove2me | solution 1 for RLHF.vonMangoldt_high_temperature_limit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:37:18.951177+00:00
-- url     : https://prove2.me/submissions/a4bb3879-c27d-4112-b5e2-9da9363c7675

-- Sol generated from NumberTheory/RLHFTemperatureLimits.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFTemperatureLimits
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_tendsto_freeEnergy_high_temperature
import Theorems.Thm_RLHF_unifRef_isPosDist
import Theorems.Thm_RLHF_unif_reward_eq_psi

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
theorem solution{N : ℕ} (hN : 0 < N) :
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
    Tendsto (fun β => freeEnergy β (vonMangoldtReward N) (unifRef N)) atTop
      (𝓝 (chebyshevPsiFin N / (N : ℝ))) := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hm : ∀ i : Fin N, (0 : ℝ) ≤ vonMangoldtReward N i := fun i => vonMangoldt_nonneg
  have hM : ∀ i : Fin N, vonMangoldtReward N i ≤ Real.log N := by
    intro i
    have h1 : Λ ((i : ℕ) + 1) ≤ Real.log (((i : ℕ) + 1 : ℕ) : ℝ) := vonMangoldt_le_log
    have h2 : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : (i : ℕ) + 1 ≤ N := i.isLt
      exact_mod_cast this
    exact le_trans h1 (Real.log_le_log (by positivity) h2)
  have := tendsto_freeEnergy_high_temperature (m := 0) (M := Real.log N)
    (unifRef_isPosDist hN) hm hM
  rwa [unif_reward_eq_psi] at this
