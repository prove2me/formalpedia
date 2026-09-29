-- Prove2me | Theorems.Thm_bernoulli_powerset_expectation_eq_product_measure_integral
-- name    : bernoulli_powerset_expectation_eq_product_measure_integral
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T03:08:03.428251+00:00
-- url     : https://prove2.me/theorems/cd98f4ce-6775-4c62-a943-bbe0a6314981
-- statement:
--   THE KEYSTONE BRIDGE between the bespoke powerset-Bernoulli sampling model and Mathlib measure theory. For the Candes-Recht matrix-completion development, the powerset expectation $\mathbb{E}_p[F] = \sum_{\Omega} p^{|\Omega|}(1-p)^{N-|\Omega|} F(\Omega)$ (bernoulliExpectation, a finite sum over all observation sets) equals the Lebesgue integral of $F$ against the stock Mathlib product measure $\mu = \mathrm{bernMeasure}\,p$ = $\mathrm{Measure.pi}$ of independent Bernoulli(p) coordinates on the indicator space $(\mathrm{Fin}\,n_1 \times \mathrm{Fin}\,n_2) \to \mathrm{Bool}$, where a sample point $\omega$ is read as the observation set indicatorToFinset $\omega = \{w : \omega(w) = \mathrm{true}\}$. Concretely: $\mathbb{E}_p[F] = \int_\omega F(\mathrm{indicatorToFinset}\,\omega)\,d\mu$. This is the keystone that makes Mathlib condExp / condExpKernel / iIndepFun and the standard concentration API directly applicable to the powerset model: the per-point product mass of Measure.pi (pi_singleton) is exactly the binomial observation weight $p^{|\Omega|}(1-p)^{N-|\Omega|}$ under the indicator-to-Finset bijection. Proof: integral over a finite measure space = sum of point-masses (integral_fintype); each point mass factorizes over coordinates (Measure.pi pi_singleton, PMF.bernoulli); reindex the sum over Bool-indicators to a sum over observation sets via indicatorFinsetEquiv; the product weight matches bernoulliObservationWeight by splitting the coordinate product over membership.
-- source:
--   Mathlib MeasureTheory.Constructions.Pi (Measure.pi_singleton), MeasureTheory.Integral.Bochner (integral_fintype), Probability.ProbabilityMassFunction (PMF.bernoulli); Candes-Recht 2009 arXiv:0805.4471 section 6 (independent Bernoulli sampling model).

import Definitions.Def_matrix_completion_bernoulli_measure
open MatrixCompletion
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

theorem bernoulli_powerset_expectation_eq_product_measure_integral
    {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1)
    (F : Finset (Fin n1 × Fin n2) → ℝ) :
    bernoulliExpectation (p : ℝ) F
      = ∫ ω, F (indicatorToFinset ω) ∂(bernMeasure p hp) := by sorry
