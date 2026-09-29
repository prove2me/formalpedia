-- Prove2me | solution 1 for RLHF.freeEnergy_antitone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:55:27.992766+00:00
-- url     : https://prove2.me/submissions/dae47712-eb82-4728-9c06-54f8886da93f

-- Sol generated from NumberTheory/RLHFTemperatureSpectrum.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_IsPosDist_isDist
import Theorems.Thm_RLHF_freeEnergy_eq_objective_gibbs
import Theorems.Thm_RLHF_gibbsPolicy_isPosDist
import Theorems.Thm_RLHF_kl_nonneg
import Theorems.Thm_RLHF_variational_principle

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








/-! ## The von Mangoldt reward model on `{1, …, N}` -/










open RLHF in
theorem solution{β₁ β₂ : ℝ} {r p : Ω → ℝ}
    (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hle : β₁ ≤ β₂) (hp : IsPosDist p) :
    freeEnergy β₂ r p ≤ freeEnergy β₁ r p := by
  set q := gibbsPolicy β₂ r p with hq_def
  have hqd : IsDist q := (gibbsPolicy_isPosDist hp).isDist
  have h2 : freeEnergy β₂ r p = (∑ y, q y * r y) - β₂ * klDiv q p := by
    rw [freeEnergy_eq_objective_gibbs hβ₂ hp, objective]
  have hkl : 0 ≤ klDiv q p := kl_nonneg hqd hp
  have hmono : (∑ y, q y * r y) - β₂ * klDiv q p ≤ (∑ y, q y * r y) - β₁ * klDiv q p := by
    have : β₁ * klDiv q p ≤ β₂ * klDiv q p := mul_le_mul_of_nonneg_right hle hkl
    linarith
  have h1 : (∑ y, q y * r y) - β₁ * klDiv q p ≤ freeEnergy β₁ r p := by
    have := variational_principle (β := β₁) (r := r) hβ₁ hp hqd
    rw [objective] at this
    exact this
  linarith [h2 ▸ hmono]
