-- Prove2me | solution 1 for RLHF.gibbs_ne_reference_of_nonconstant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:13:31.024198+00:00
-- url     : https://prove2.me/submissions/2ec81f48-27ca-4f7c-a5c2-b0246a8744ee

-- Sol generated from NumberTheory/RLHFTemperatureSpectrum.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_partition_pos

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
theorem solution{β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β)
    (hp : IsPosDist p) {y z : Ω} (hyz : r y ≠ r z) : gibbsPolicy β r p ≠ p := by
  intro hEq
  have hZ := partition_pos (β := β) (r := r) hp
  have key : ∀ w, Real.exp (r w / β) = partition β r p := by
    intro w
    have hw : p w * Real.exp (r w / β) / partition β r p = p w := congrFun hEq w
    have hpw := hp.1 w
    rw [div_eq_iff (ne_of_gt hZ)] at hw
    exact mul_left_cancel₀ (ne_of_gt hpw) (by linarith [hw] : p w * Real.exp (r w / β) = p w * partition β r p)
  have h1 := key y
  have h2 := key z
  have hdiv : r y / β = r z / β := Real.exp_injective (h1.trans h2.symm)
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  apply hyz
  field_simp at hdiv
  linarith
