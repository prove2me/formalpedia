-- Prove2me | Theorems.Thm_FactoringLab_randomized_barrier_eq_iff
-- name    : FactoringLab.randomized_barrier_eq_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:32:54.208033+00:00
-- url     : https://prove2.me/theorems/846c7f6c-d274-4e40-a894-a0e14be7b49c
-- title:
--   Tightness of the randomized barrier.
-- statement:
--   **Tightness of the randomized barrier.**  Equality holds exactly for the
--   degenerate mixtures: those all of whose positively weighted strategies
--   reproduce the band mean on the whole population.
--
--   ```lean
--   theorem FactoringLab.randomized_barrier_eq_iff[DecidableEq κ] {m : ℕ} (Ω : Finset ι) (n : ι → κ)
--       (Y : ι → ℝ) (w : Fin m → ℝ) (T : Fin m → DTree ι) (hw : ∑ j, w j = 1)
--       (hw0 : ∀ j, 0 ≤ w j) (hT : ∀ j, (T j).BandOnly Ω n) :
--       mixRisk Ω w T Y = ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2 ↔
--         ∀ j, 0 < w j → ∀ i ∈ Ω, (T j).eval i = bandMean Ω n Y i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/RandomizedBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/RandomizedBarrier.lean#L164

-- Thm stub generated from Probability/RandomizedBarrier.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveBarrier
import Definitions.Def_Probability_RandomizedBarrier
import Definitions.Def_Probability_StructuralOrthogonality
/-
# The randomized barrier (Factoring Lab, Phase A v19c — cycle 3)

This file closes the first (deterministic-reduction) half of **Conjecture D** of
`FUTURE_DIRECTIONS.md`: randomization does not break the structural barrier.

`Catalog/Probability/AdaptiveBarrier.lean` proves that a *single* adaptive
strategy whose tests and outputs are band-measurable cannot predict the hidden
factor better than the band mean.  A natural escape route is to randomize: run
a finite mixture `μ = (w_1, …, w_m)` over strategies `t_1, …, t_m` and hope that
the mixture beats every one of its members.  It cannot, and the reason is
sharper than convexity alone:

* `FactoringLab.mix_sq_error_decomposition` — an exact *bias–variance identity*
  for mixtures: the expected squared error of the randomized strategy equals
  the squared error of its **mean predictor** `m(i) = Σ_j w_j t_j(i)` plus the
  randomization variance `Σ_i Σ_j w_j (t_j(i) − m(i))²`.  Randomizing therefore
  *strictly increases* the error unless all strategies with positive weight
  agree pointwise on the population (`FactoringLab.randomization_never_helps`,
  `FactoringLab.randomization_strictly_hurts`).
* `FactoringLab.mixEval_bandMeasurable` — the mean predictor of a mixture of
  band-measurable strategies is itself band-measurable, so it factors through
  the band label (`FactoringLab.randomized_is_N_only`) and is dominated by the
  band mean.
* `FactoringLab.randomized_barrier` — consequently the expected squared error of
  *any* finite mixture of `N`-only adaptive strategies is at least the
  irreducible band-conditional error, uniformly in the number of strategies,
  their sizes and the mixing weights.
* `FactoringLab.randomized_barrier_eq_iff` — the barrier is *tight exactly* on
  the degenerate mixtures: equality holds iff every strategy carrying positive
  weight reproduces the band mean on the whole population.  This is the
  equality clause conjectured in Conjecture D.

Together with `FactoringLab.adaptive_barrier`, this says: neither adaptivity nor
randomness — nor any combination of the two — extracts information about the
hidden factor beyond what the band label already carries.
-/

open Finset

open FactoringLab

variable {ι κ : Type*}

/-! ### Mixtures of strategies -/





/-! ### The bias–variance identity for mixtures -/

theorem FactoringLab.randomized_barrier_eq_iff[DecidableEq κ] {m : ℕ} (Ω : Finset ι) (n : ι → κ)
    (Y : ι → ℝ) (w : Fin m → ℝ) (T : Fin m → DTree ι) (hw : ∑ j, w j = 1)
    (hw0 : ∀ j, 0 ≤ w j) (hT : ∀ j, (T j).BandOnly Ω n) :
    mixRisk Ω w T Y = ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2 ↔
      ∀ j, 0 < w j → ∀ i ∈ Ω, (T j).eval i = bandMean Ω n Y i := by sorry
