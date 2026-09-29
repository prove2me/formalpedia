-- Prove2me | Theorems.Thm_RLHF_expSum_sq_le
-- name    : RLHF.expSum_sq_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:40:38.707576+00:00
-- url     : https://prove2.me/theorems/8442a856-63d6-4233-8cc1-1a2232007f7a
-- title:
--   Midpoint log-convexity of the partition function, by Cauchy–Schwarz.
-- statement:
--   **Midpoint log-convexity of the partition function**, by Cauchy–Schwarz.
--
--   ```lean
--   theorem RLHF.expSum_sq_le{r p : Ω → ℝ} (hp : ∀ y, 0 ≤ p y) (s t : ℝ) :
--       expSum r p ((s + t) / 2) ^ 2 ≤ expSum r p s * expSum r p t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFLogConvexity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFLogConvexity.lean#L48

-- Thm stub generated from NumberTheory/RLHFLogConvexity.lean
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




omit [Nonempty Ω] in

theorem RLHF.expSum_sq_le{r p : Ω → ℝ} (hp : ∀ y, 0 ≤ p y) (s t : ℝ) :
    expSum r p ((s + t) / 2) ^ 2 ≤ expSum r p s * expSum r p t := by sorry
