-- Prove2me | solution 1 for RLHF.expSum_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:34:40.888679+00:00
-- url     : https://prove2.me/submissions/20586cdc-90c6-4c5b-b847-6c65b83ed28b

-- Sol generated from NumberTheory/RLHFLogConvexity.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFLogConvexity
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum

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







open RLHF in
omit [Nonempty Ω] in
theorem solution{r p : Ω → ℝ} (hp : ∀ y, 0 ≤ p y) (s t : ℝ) :
    expSum r p ((s + t) / 2) ^ 2 ≤ expSum r p s * expSum r p t := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul univ
    (fun y _ => by have := hp y; positivity) (fun y _ => by have := hp y; positivity)
    (fun y _ => ?_)
  have hexp : Real.exp (r y * ((s + t) / 2)) ^ 2
      = Real.exp (r y * s) * Real.exp (r y * t) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc (p y * Real.exp (r y * ((s + t) / 2))) ^ 2
      = p y ^ 2 * Real.exp (r y * ((s + t) / 2)) ^ 2 := by ring
    _ = (p y * Real.exp (r y * s)) * (p y * Real.exp (r y * t)) := by rw [hexp]; ring
