-- Prove2me | Theorems.Thm_TreatmentLocality_integral_eq_integral_stepLaw
-- name    : TreatmentLocality.integral_eq_integral_stepLaw
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T01:58:28.168831+00:00
-- url     : https://prove2.me/theorems/a76f3fd2-c79d-4516-821e-ce87cfec0431
-- title:
--   Stationary decomposition of the experiment chain
-- statement:
--   **The stationary decomposition of the experiment chain.** Let $\nu$ be an invariant law of the experiment chain of arXiv:2407.19618: a law on the sample space of one step $z = (s, \gamma, s', r)$ that is fixed by the transition kernel. Then for every integrable observable $f$,
--   $$\mathbb{E}_\nu[f] \;=\; \mathbb{E}_\nu\Bigl[\;\int f(s_z, p)\, \mathrm{d}\,\mathrm{stepLaw}(s_z)(p)\Bigr],$$
--   where $s_z$ is the *current* state of $z$ and $\mathrm{stepLaw}(s)$ is the law of the triple (arm, next state, reward) produced by the mixed policy $\pi^{1/2}$ at $s$.
--
--   In words: under an invariant law the step may be resampled from the one-step experiment law at its own current state, so $\nu$ factorises as the stationary state distribution tensored with the step law. Two facts combine: the kernel produces a new step by drawing from the step law at the *next* state of the old one, and — again by invariance — the current state and the next state have the same distribution. This is the identity that lets population quantities of the experiment be computed state by state.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3: §3 Algorithm 1 (the mixed policy π^{1/2} and the experiment trajectory), §6.2 (the information-sharing statistics K^a_IS, R^a_IS and their limits Diag(μ^{1/2})P^a and Diag(μ^{1/2})r^a), Remark 1 and Proposition 5 (the model-based plug-in estimator), and Appendix EC.3.1-EC.3.2.

import Definitions.Def_TreatmentLocalityPlugIn
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.integral_eq_integral_stepLaw {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    {f : Step S → ℝ} (hf : Measurable f) (hint : Integrable f ν) :
    ∫ z, f z ∂ν = ∫ z, (∫ p, f (Step.state z, p) ∂(stepLaw M (Step.state z))) ∂ν := by sorry
