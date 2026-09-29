-- Prove2me | Theorems.Thm_RLHF_freeEnergy_harmonic_le
-- name    : RLHF.freeEnergy_harmonic_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:43:24.688401+00:00
-- url     : https://prove2.me/theorems/f023b148-5dc4-4021-8fd6-9e4ac15641a7
-- title:
--   The harmonic annealing inequality.
-- statement:
--   **The harmonic annealing inequality.**  If `β⁻¹` is the average of `β₁⁻¹` and `β₂⁻¹`,
--   then the normalized alignment value at `β` is at most the average of the normalized values
--   at `β₁` and `β₂`.
--
--   ```lean
--   theorem RLHF.freeEnergy_harmonic_le{β β₁ β₂ : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hβ₁ : 0 < β₁)
--       (hβ₂ : 0 < β₂) (hp : IsPosDist p) (hmean : β⁻¹ = (β₁⁻¹ + β₂⁻¹) / 2) :
--       freeEnergy β r p / β ≤ (freeEnergy β₁ r p / β₁ + freeEnergy β₂ r p / β₂) / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFLogConvexity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFLogConvexity.lean#L63

-- Thm stub generated from NumberTheory/RLHFLogConvexity.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
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

theorem RLHF.freeEnergy_harmonic_le{β β₁ β₂ : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hp : IsPosDist p) (hmean : β⁻¹ = (β₁⁻¹ + β₂⁻¹) / 2) :
    freeEnergy β r p / β ≤ (freeEnergy β₁ r p / β₁ + freeEnergy β₂ r p / β₂) / 2 := by sorry
