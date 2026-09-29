-- Prove2me | solution 1 for RLHF.freeEnergy_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:58:43.079164+00:00
-- url     : https://prove2.me/submissions/6a9d9c1f-971e-4496-9290-0db22ec4833a

-- Sol generated from NumberTheory/RLHFTemperatureSpectrum.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_IsPosDist_isDist
import Theorems.Thm_RLHF_freeEnergy_eq_objective_gibbs
import Theorems.Thm_RLHF_gibbsPolicy_isPosDist
import Theorems.Thm_RLHF_kl_nonneg

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
theorem solution{β M : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsPosDist p)
    (hM : ∀ y, r y ≤ M) : freeEnergy β r p ≤ M := by
  set q := gibbsPolicy β r p with hq_def
  have hqd : IsDist q := (gibbsPolicy_isPosDist hp).isDist
  have hrew : ∑ y, q y * r y ≤ M := by
    have hterm : ∀ y ∈ (univ : Finset Ω), q y * r y ≤ q y * M :=
      fun y _ => mul_le_mul_of_nonneg_left (hM y) (hqd.1 y)
    have := Finset.sum_le_sum hterm
    rwa [← Finset.sum_mul, hqd.2, one_mul] at this
  have hkl : 0 ≤ klDiv q p := kl_nonneg hqd hp
  have := freeEnergy_eq_objective_gibbs (β := β) (r := r) hβ hp
  rw [this, objective]
  nlinarith
