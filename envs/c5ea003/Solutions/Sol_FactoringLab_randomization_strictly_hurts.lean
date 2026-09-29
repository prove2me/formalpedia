-- Prove2me | solution 1 for FactoringLab.randomization_strictly_hurts
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:55:38.42984+00:00
-- url     : https://prove2.me/submissions/72d69341-9efe-4b79-a5ff-71b7f18f0d13

-- Sol generated from Probability/RandomizedBarrier.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveBarrier
import Definitions.Def_Probability_RandomizedBarrier
import Theorems.Thm_FactoringLab_mix_sq_error_pointwise
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


/-- **Bias–variance decomposition for randomized strategies.**  The expected
squared error of a mixture is the squared error of its mean predictor plus the
randomization variance.  The identity is exact and needs only that the mixing
weights sum to `1`. -/
theorem mix_sq_error_decomposition {m : ℕ} (Ω : Finset ι) (w : Fin m → ℝ)
    (T : Fin m → DTree ι) (Y : ι → ℝ) (hw : ∑ j, w j = 1) :
    mixRisk Ω w T Y
      = ∑ i ∈ Ω, (mixEval w T i - Y i) ^ 2
        + ∑ i ∈ Ω, ∑ j, w j * ((T j).eval i - mixEval w T i) ^ 2 := by
  have hswap : mixRisk Ω w T Y = ∑ i ∈ Ω, ∑ j, w j * ((T j).eval i - Y i) ^ 2 := by
    unfold mixRisk
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact mix_sq_error_pointwise w (fun j => (T j).eval i) (Y i) hw






open FactoringLab in
theorem solution{m : ℕ} (Ω : Finset ι) (w : Fin m → ℝ)
    (T : Fin m → DTree ι) (Y : ι → ℝ) (hw : ∑ j, w j = 1) (hw0 : ∀ j, 0 ≤ w j)
    {i₀ : ι} (hi₀ : i₀ ∈ Ω) {j₀ : Fin m} (hj₀ : 0 < w j₀)
    (hne : (T j₀).eval i₀ ≠ mixEval w T i₀) :
    ∑ i ∈ Ω, (mixEval w T i - Y i) ^ 2 < mixRisk Ω w T Y := by
  rw [mix_sq_error_decomposition Ω w T Y hw]
  have hd : (T j₀).eval i₀ - mixEval w T i₀ ≠ 0 := sub_ne_zero.mpr hne
  have hsq : 0 < ((T j₀).eval i₀ - mixEval w T i₀) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hd))
  have hinner : 0 < ∑ j, w j * ((T j).eval i₀ - mixEval w T i₀) ^ 2 :=
    Finset.sum_pos' (fun j _ => mul_nonneg (hw0 j) (sq_nonneg _))
      ⟨j₀, Finset.mem_univ j₀, mul_pos hj₀ hsq⟩
  have hpos : 0 < ∑ i ∈ Ω, ∑ j, w j * ((T j).eval i - mixEval w T i) ^ 2 :=
    Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hw0 j) (sq_nonneg _))
      ⟨i₀, hi₀, hinner⟩
  linarith
