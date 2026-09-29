-- Prove2me | solution 1 for FactoringLab.mix_sq_error_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:50:28.086515+00:00
-- url     : https://prove2.me/submissions/451ede55-8b1d-409d-a5aa-5fe347c77f5c

-- Sol generated from Probability/RandomizedBarrier.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveBarrier
import Definitions.Def_Probability_RandomizedBarrier
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








open FactoringLab in
theorem solution{m : ℕ} (w x : Fin m → ℝ) (y : ℝ) (hw : ∑ j, w j = 1) :
    ∑ j, w j * (x j - y) ^ 2
      = (∑ j, w j * x j - y) ^ 2 + ∑ j, w j * (x j - ∑ j', w j' * x j') ^ 2 := by
  set M := ∑ j, w j * x j with hM
  have h0 : ∑ j, w j * (x j - M) = 0 := by
    have : ∑ j, w j * (x j - M) = (∑ j, w j * x j) - (∑ j, w j) * M := by
      rw [Finset.sum_mul]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hw, ← hM]
    ring
  calc ∑ j, w j * (x j - y) ^ 2
      = ∑ j, (w j * (x j - M) ^ 2 + 2 * (M - y) * (w j * (x j - M)) + (M - y) ^ 2 * w j) :=
        Finset.sum_congr rfl fun j _ => by rw [hM]; ring
    _ = (∑ j, w j * (x j - M) ^ 2) + 2 * (M - y) * (∑ j, w j * (x j - M))
          + (M - y) ^ 2 * ∑ j, w j := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (M - y) ^ 2 + ∑ j, w j * (x j - M) ^ 2 := by rw [h0, hw]; ring
