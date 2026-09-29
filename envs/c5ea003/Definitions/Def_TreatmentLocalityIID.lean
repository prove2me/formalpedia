-- Prove2me | Definitions.Def_TreatmentLocalityIID
-- name    : TreatmentLocalityIID
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T15:18:21.932595+00:00
-- url     : https://prove2.me/theorems/32d564e4-c5ff-41d1-b0fe-eff90064fa20
-- title:
--   The i.i.d. observation law of the SST experiment
-- statement:
--   **The i.i.d. reading of the SST experiment.** In the efficiency analysis of arXiv:2407.19618 the experiment is run from the stationary initial distribution $\mu^{1/2}$, and the paper then treats the observations $(s_i, a_i, s_{i+1}, r_i)$ as independent draws from a single law. That law is the one defined here: draw a state $s$ from the fixed marginal $\mu$, flip the fair coin of the mixed policy, execute the resulting action, and draw the next state and the reward from the corresponding transition and reward laws. A sample of size $T$ is the $T$-fold product of that law.
--
--   The state marginal $\mu$ is held fixed; what the experimenter does not know — and what the Cramér-Rao bound is stated against — are the transition probabilities and the reward means. Splitting the observation law this way is what makes the Fisher information of a sample of size $T$ equal to $T$ times the Fisher information of one observation, which is the form the information inequality is applied in.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Appendix EC.4.3 (proof of Theorem 5): "Since we assume the initial distribution is mu^{1/2}, the observations (s_i, a_i, s_{i+1}, r_i) in tau can be seen as i.i.d."

import Definitions.Def_TreatmentLocality
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Constructions.Pi

/-!
The i.i.d. reading of the SST experiment: one observation drawn from the stationary
one-step law, and a sample of `T` independent observations.

Source: Chen, Simchi-Levi, Wang, *Improving the Estimation of Lifetime Effects in A/B
Testing via Treatment Locality* (arXiv:2407.19618), Appendix EC.4.3: "Since we assume the
initial distribution is `μ^{1/2}`, the observations `(sᵢ, aᵢ, sᵢ₊₁, rᵢ)` in `τ` can be seen
as i.i.d."  The state marginal `μ` is held fixed; the unknown parameters are the
transition probabilities and the reward means.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The kernel producing one experiment observation `(s, γ, s', r)` from the current
state `s`: the state is recorded, and the arm, next state and reward are drawn from the
one-step experiment law at `s`. -/
noncomputable def obsKernel (M : Model S) : Kernel S (Step S) :=
  (Kernel.id).prod (stepKernel M)

instance obsKernel.instIsMarkovKernel (M : Model S) : IsMarkovKernel (obsKernel M) := by
  rw [obsKernel]; infer_instance

@[simp] lemma obsKernel_apply (M : Model S) (s : S) :
    obsKernel M s = (Measure.dirac s).prod (stepLaw M s) := by
  rw [obsKernel, Kernel.prod_apply, Kernel.id_apply]
  rfl

/-- The law of one experiment observation when the current state is drawn from `μ`. -/
noncomputable def obsLaw (M : Model S) (μ : Measure S) : Measure (Step S) :=
  μ.bind (obsKernel M)

instance obsLaw.instIsProbabilityMeasure (M : Model S) (μ : Measure S)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (obsLaw M μ) := by
  rw [obsLaw]; infer_instance

/-- The law of a sample of `T` independent experiment observations. -/
noncomputable def sampleLaw (M : Model S) (μ : Measure S) (T : ℕ) :
    Measure (Fin T → Step S) :=
  Measure.pi fun _ => obsLaw M μ

instance sampleLaw.instIsProbabilityMeasure (M : Model S) (μ : Measure S)
    [IsProbabilityMeasure μ] (T : ℕ) : IsProbabilityMeasure (sampleLaw M μ T) := by
  rw [sampleLaw]; infer_instance

end TreatmentLocality


