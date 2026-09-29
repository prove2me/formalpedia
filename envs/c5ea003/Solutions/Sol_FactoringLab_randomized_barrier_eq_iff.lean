-- Prove2me | solution 1 for FactoringLab.randomized_barrier_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:55:38.920954+00:00
-- url     : https://prove2.me/submissions/e966b305-d09d-42fe-99a8-7511b598d718

-- Sol generated from Probability/RandomizedBarrier.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveBarrier
import Definitions.Def_Probability_RandomizedBarrier
import Definitions.Def_Probability_StructuralOrthogonality
import Theorems.Thm_FactoringLab_adaptive_barrier
import Theorems.Thm_FactoringLab_adaptive_sq_error_decomposition
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
theorem solution[DecidableEq κ] {m : ℕ} (Ω : Finset ι) (n : ι → κ)
    (Y : ι → ℝ) (w : Fin m → ℝ) (T : Fin m → DTree ι) (hw : ∑ j, w j = 1)
    (hw0 : ∀ j, 0 ≤ w j) (hT : ∀ j, (T j).BandOnly Ω n) :
    mixRisk Ω w T Y = ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2 ↔
      ∀ j, 0 < w j → ∀ i ∈ Ω, (T j).eval i = bandMean Ω n Y i := by
  classical
  set E := ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2 with hE
  have hstep : ∀ j, 0 ≤ (∑ i ∈ Ω, ((T j).eval i - Y i) ^ 2) - E := fun j => by
    have := adaptive_barrier Ω n Y (T j) (hT j)
    linarith
  constructor
  · intro heq j hj i hi
    have hzero : ∑ j', w j' * ((∑ i ∈ Ω, ((T j').eval i - Y i) ^ 2) - E) = 0 := by
      have hexp : ∑ j', w j' * ((∑ i ∈ Ω, ((T j').eval i - Y i) ^ 2) - E)
          = mixRisk Ω w T Y - (∑ j', w j') * E := by
        unfold mixRisk
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j' _ => by ring
      rw [hexp, hw, one_mul, heq]
      ring
    have hterm : ∀ j', j' ∈ Finset.univ →
        w j' * ((∑ i ∈ Ω, ((T j').eval i - Y i) ^ 2) - E) = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun j' _ => ?_).1 hzero
      exact mul_nonneg (hw0 j') (hstep j')
    have hj' : (∑ i ∈ Ω, ((T j).eval i - Y i) ^ 2) - E = 0 := by
      rcases mul_eq_zero.1 (hterm j (Finset.mem_univ j)) with h | h
      · exact absurd h (ne_of_gt hj)
      · exact h
    have hdec := adaptive_sq_error_decomposition Ω n Y (T j) (hT j)
    have hsq : ∑ i ∈ Ω, ((T j).eval i - bandMean Ω n Y i) ^ 2 = 0 := by
      rw [hE] at hj'
      linarith [hdec, hj']
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg
      ((T j).eval i - bandMean Ω n Y i)).1 hsq i hi
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · intro hall
    have hrisk : ∀ j, 0 ≤ w j → w j * ∑ i ∈ Ω, ((T j).eval i - Y i) ^ 2 = w j * E := by
      intro j _
      rcases eq_or_lt_of_le (hw0 j) with h | h
      · rw [← h]; ring
      · congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hall j h i hi]
    unfold mixRisk
    rw [Finset.sum_congr rfl fun j _ => hrisk j (hw0 j), ← Finset.sum_mul, hw, one_mul]
