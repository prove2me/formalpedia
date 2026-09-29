-- Prove2me | Theorems.Thm_BanditAlgorithm_least_squares_confidence_ellipsoid
-- name    : BanditAlgorithm.least_squares_confidence_ellipsoid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T00:22:02.849866+00:00
-- url     : https://prove2.me/theorems/a2fd89e1-9aab-4b91-a448-f5f3723ceeed
-- statement:
--   (Confidence ellipsoid; L&S Theorem 20.5) With the setup above and rewards $X_{t+1} = \langle \theta_*, A_{t+1}\rangle + \eta_{t+1}$, let
--
--   $$\hat\theta_t = V_t(\lambda)^{-1} \sum_{s=1}^t X_s A_s$$
--
--   be the $\lambda$-regularized least-squares estimator ($\lambda > 0$). For $\delta \in (0,1)$, with probability at least $1 - \delta$, simultaneously for all $t \in \mathbb{N}$:
--
--   $$\|\hat\theta_t - \theta_*\|_{V_t(\lambda)} < \sqrt{\lambda}\,\|\theta_*\|_2 + \sqrt{2\log\frac{1}{\delta} + \log\frac{\det V_t(\lambda)}{\lambda^d}},$$
--
--   where $\|v\|_M = \sqrt{v^\top M v}$.
-- source:
--   L&S Theorem 20.5, p.260

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Definitions.Def_SelfNormalizedProcess


open MeasureTheory ProbabilityTheory Matrix

theorem BanditAlgorithm.least_squares_confidence_ellipsoid
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ) (X : ℕ → Ω → ℝ) (θs : Fin d → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    (hX : ∀ (t : ℕ) (ω : Ω), X (t + 1) ω = θs ⬝ᵥ A (t + 1) ω + η (t + 1) ω)
    {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    1 - δ ≤ P.real {ω | ∀ t : ℕ,
        Real.sqrt ((regularizedLeastSquares d lam A X t ω - θs) ⬝ᵥ
            regularizedDesignMatrix d lam A t ω *ᵥ
              (regularizedLeastSquares d lam A X t ω - θs))
          < Real.sqrt lam * Real.sqrt (θs ⬝ᵥ θs)
            + Real.sqrt (2 * Real.log (1 / δ)
                + Real.log ((regularizedDesignMatrix d lam A t ω).det / lam ^ d))} := by
  sorry
