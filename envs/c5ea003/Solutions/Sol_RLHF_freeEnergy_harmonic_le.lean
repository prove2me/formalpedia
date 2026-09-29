-- Prove2me | solution 1 for RLHF.freeEnergy_harmonic_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:58:41.996001+00:00
-- url     : https://prove2.me/submissions/1fd061ea-8d23-42eb-9b78-1cd5239985c9

-- Sol generated from NumberTheory/RLHFLogConvexity.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFLogConvexity
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_expSum_sq_le

/-!
# Log-convexity of the RLHF partition function

The partition function of an RLHF problem, read as a function of the *inverse* KL
coefficient `t = β⁻¹`,

```
expSum r p t = ∑_y p y · exp (r y · t),
```

is log-convex.  This file proves the midpoint form of that statement by Cauchy–Schwarz and
transports it to the free energy, giving the *harmonic annealing inequality*: the normalized
alignment value `V(β)/β` at the harmonic mean of two KL coefficients is dominated by the
average of the endpoint values.

Main results:

* `RLHF.expSum_sq_le` — midpoint log-convexity of the exponential sum;
* `RLHF.partition_eq_expSum` — the partition function at KL coefficient `β` is the
  exponential sum at inverse temperature `β⁻¹`;
* `RLHF.freeEnergy_harmonic_le` — the harmonic annealing inequality for the free energy.

The full (differential) convexity statement, together with the identification of the
curvature with the reward variance, is proved downstream in `RLHFVarianceCurvature`.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]


omit [Nonempty Ω] in
/-- The partition function at KL coefficient `β` is the exponential sum at `β⁻¹`. -/
theorem partition_eq_expSum (β : ℝ) (r p : Ω → ℝ) : partition β r p = expSum r p β⁻¹ := by
  unfold partition expSum
  exact Finset.sum_congr rfl fun y _ => by rw [div_eq_mul_inv]

theorem expSum_pos {r p : Ω → ℝ} (hp : ∀ y, 0 < p y) (t : ℝ) : 0 < expSum r p t :=
  Finset.sum_pos (fun y _ => by have := hp y; positivity) univ_nonempty




open RLHF in
theorem solution{β β₁ β₂ : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hp : IsPosDist p) (hmean : β⁻¹ = (β₁⁻¹ + β₂⁻¹) / 2) :
    freeEnergy β r p / β ≤ (freeEnergy β₁ r p / β₁ + freeEnergy β₂ r p / β₂) / 2 := by
  have hnorm : ∀ γ : ℝ, 0 < γ → freeEnergy γ r p / γ = Real.log (expSum r p γ⁻¹) := by
    intro γ hγ
    unfold freeEnergy
    rw [partition_eq_expSum, mul_comm, mul_div_assoc, div_self (ne_of_gt hγ), mul_one]
  have h1 : 0 < expSum r p β₁⁻¹ := expSum_pos hp.1 _
  have h2 : 0 < expSum r p β₂⁻¹ := expSum_pos hp.1 _
  have h0 : 0 < expSum r p β⁻¹ := expSum_pos hp.1 _
  have hsq : expSum r p β⁻¹ ^ 2 ≤ expSum r p β₁⁻¹ * expSum r p β₂⁻¹ := by
    rw [hmean]
    exact expSum_sq_le (fun y => (hp.1 y).le) _ _
  have hlog : Real.log (expSum r p β⁻¹ ^ 2)
      ≤ Real.log (expSum r p β₁⁻¹ * expSum r p β₂⁻¹) :=
    Real.log_le_log (by positivity) hsq
  rw [Real.log_pow, Real.log_mul (ne_of_gt h1) (ne_of_gt h2)] at hlog
  rw [hnorm β hβ, hnorm β₁ hβ₁, hnorm β₂ hβ₂]
  push_cast at hlog
  linarith
