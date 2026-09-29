-- Prove2me | solution 1 for RLHF.kl_budget
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:13:32.10919+00:00
-- url     : https://prove2.me/submissions/1eddcc85-c164-40bc-8370-8f347254f322

-- Sol generated from NumberTheory/RLHFTemperatureLimits.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureLimits
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_IsPosDist_isDist
import Theorems.Thm_RLHF_freeEnergy_eq_objective_gibbs
import Theorems.Thm_RLHF_freeEnergy_ge_reference
import Theorems.Thm_RLHF_gibbsPolicy_isPosDist

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
theorem solution{β m M : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hm : ∀ y, m ≤ r y) (hM : ∀ y, r y ≤ M) :
    β * klDiv (gibbsPolicy β r p) p ≤ M - m := by
  set q := gibbsPolicy β r p with hq_def
  have hqd : IsDist q := (gibbsPolicy_isPosDist hp).isDist
  have hval : objective β r p q = freeEnergy β r p := (freeEnergy_eq_objective_gibbs hβ hp).symm
  have href : ∑ y, p y * r y ≤ freeEnergy β r p := freeEnergy_ge_reference hβ hp
  have hup : ∑ y, q y * r y ≤ M := by
    have hterm : ∀ y ∈ (univ : Finset Ω), q y * r y ≤ q y * M :=
      fun y _ => mul_le_mul_of_nonneg_left (hM y) (hqd.1 y)
    have := Finset.sum_le_sum hterm
    rwa [← Finset.sum_mul, hqd.2, one_mul] at this
  have hlow : m ≤ ∑ y, p y * r y := by
    have hterm : ∀ y ∈ (univ : Finset Ω), p y * m ≤ p y * r y :=
      fun y _ => mul_le_mul_of_nonneg_left (hm y) (hp.1 y).le
    have := Finset.sum_le_sum hterm
    rwa [← Finset.sum_mul, hp.2, one_mul] at this
  rw [objective] at hval
  linarith
