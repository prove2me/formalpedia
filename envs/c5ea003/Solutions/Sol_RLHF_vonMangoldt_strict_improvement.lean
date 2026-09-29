-- Prove2me | solution 1 for RLHF.vonMangoldt_strict_improvement
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:37:20.82638+00:00
-- url     : https://prove2.me/submissions/7db8fc39-d033-4da3-bf77-7ada12993a1f

-- Sol generated from NumberTheory/RLHFTemperatureSpectrum.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_IsPosDist_isDist
import Theorems.Thm_RLHF_gibbs_ne_reference_of_nonconstant
import Theorems.Thm_RLHF_kl_eq_zero_iff
import Theorems.Thm_RLHF_unifRef_isPosDist
import Theorems.Thm_RLHF_unif_reward_eq_psi
import Theorems.Thm_RLHF_variational_strict

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







/-- **Strict improvement.**  Whenever the reward model is non-constant, KL-regularized
RLHF strictly beats the SFT reference, at every finite temperature. -/
theorem strict_improvement {β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    {y z : Ω} (hyz : r y ≠ r z) : ∑ w, p w * r w < freeEnergy β r p := by
  have hne : p ≠ gibbsPolicy β r p :=
    fun h => gibbs_ne_reference_of_nonconstant hβ hp hyz h.symm
  have := variational_strict hβ hp hp.isDist hne
  rw [objective, (kl_eq_zero_iff hp.isDist hp).mpr rfl] at this
  simpa [freeEnergy] using this

/-! ## The von Mangoldt reward model on `{1, …, N}` -/










open RLHF in
theorem solution{β : ℝ} {N : ℕ} (hβ : 0 < β) (hN : 2 ≤ N) :
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
    chebyshevPsiFin N / (N : ℝ) < freeEnergy β (vonMangoldtReward N) (unifRef N) := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega : 0 < N)
  have hN0 : 0 < N := by omega
  have hy : vonMangoldtReward N ⟨0, by omega⟩ = 0 := by
    simp [vonMangoldtReward, vonMangoldt_apply_one]
  have hz : vonMangoldtReward N ⟨1, by omega⟩ = Real.log 2 := by
    have h2 : Λ 2 = Real.log 2 := by
      simpa using vonMangoldt_apply_prime Nat.prime_two
    simpa [vonMangoldtReward] using h2
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hne : vonMangoldtReward N ⟨0, by omega⟩ ≠ vonMangoldtReward N ⟨1, by omega⟩ := by
    rw [hy, hz]; exact ne_of_lt hlog2
  have := strict_improvement (β := β) (r := vonMangoldtReward N) hβ (unifRef_isPosDist hN0) hne
  rwa [unif_reward_eq_psi] at this
