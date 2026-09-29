-- Prove2me | Definitions.Def_Probability_RandomizedBarrier
-- name    : Probability_RandomizedBarrier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:54.109184+00:00
-- url     : https://prove2.me/theorems/a4a88a54-288e-4933-bf38-82e76a6db435
-- title:
--   Aether Catalog definitions — Probability_RandomizedBarrier
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.RandomizedBarrier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/RandomizedBarrier.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_AdaptiveBarrier
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

namespace FactoringLab

variable {ι κ : Type*}

/-! ### Mixtures of strategies -/

/-- The **mean predictor** of a randomized strategy: the mixture `Σ_j w_j t_j`
of the outputs of finitely many strategies. -/
noncomputable def mixEval {m : ℕ} (w : Fin m → ℝ) (T : Fin m → DTree ι) (i : ι) : ℝ :=
  ∑ j, w j * (T j).eval i

/-- The expected squared error of the randomized strategy `(w, T)`: the average,
over the mixing distribution, of the squared errors of its members. -/
noncomputable def mixRisk {m : ℕ} (Ω : Finset ι) (w : Fin m → ℝ) (T : Fin m → DTree ι)
    (Y : ι → ℝ) : ℝ :=
  ∑ j, w j * ∑ i ∈ Ω, ((T j).eval i - Y i) ^ 2



/-! ### The bias–variance identity for mixtures -/







end FactoringLab


