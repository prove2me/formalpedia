-- Prove2me | solution 1 for BanditAlgorithm.mdp_integral_trajectory_succ
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T04:32:08.041583+00:00
-- url     : https://prove2.me/submissions/785bbdaa-3491-475b-b4fc-4d9675033366

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory BanditAlgorithm

/-- **One step of the MDP interaction protocol** (L&S Fig. 38.1): integrating a
function of a trajectory of `n + 1` rounds is integrating over the first `n`
rounds and then over the pair `(S_{n+1}, A_{n+1})` drawn from the step kernel.

Every function on the trajectory space is integrable, because the space is
finite; the proof is therefore the change of variables along `Fin.snoc`
followed by the Fubini property of the composition-product. -/
theorem solution {S A : ℕ} (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ)
    (F : MDPTrajectory S A (n + 1) → ℝ) :
    ∫ h, F h ∂(mdpMeasure M μ0 π (n + 1))
      = ∫ h, (∫ p, F (Fin.snoc h p) ∂(mdpStepKernel M μ0 π n h))
          ∂(mdpMeasure M μ0 π n) := by
  rw [mdpMeasure, integral_map measurable_mdpTrajectorySnoc.aemeasurable
      (Integrable.of_finite (f := F)).aestronglyMeasurable,
    Measure.integral_compProd (Integrable.of_finite)]
