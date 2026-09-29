-- Prove2me | Theorems.Thm_Statistics_gaussianReal_shift
-- name    : Statistics.gaussianReal_shift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:32:21.617859+00:00
-- url     : https://prove2.me/theorems/741c6ab2-5dde-4c27-9702-72d4990a6c2e
-- title:
--   Likelihood ratio of a Gaussian mean shift (Cameron–Martin)
-- statement:
--   **The likelihood ratio of a Gaussian mean shift.** For $v > 0$ and any $h \in \mathbb{R}$,
--   $$\mathcal{N}(m+h, v) \;=\; \mathcal{N}(m, v)\cdot L_h, \qquad L_h(r) \;=\; \exp\Bigl(\frac{h(r-m)}{v} - \frac{h^2}{2v}\Bigr),$$
--   where $\mu \cdot L$ denotes $\mathrm{withDensity}$. Equivalently $\mathrm{d}\mathcal{N}(m+h,v)/\mathrm{d}\mathcal{N}(m,v) = L_h$: the two Gaussians are mutually absolutely continuous and the density is the exponential tilt with natural parameter $h/v$ and cumulant $h^2/2v$. Note $\mathbb{E}_{\mathcal{N}(m,v)}[L_h] = 1$ and $\partial_h L_h|_{h=0}(r) = (r-m)/v$, the score of the Gaussian location family, whose second moment is the Fisher information $1/v$. This is the finite-dimensional Cameron-Martin formula and the computational core of every Cramér-Rao bound for a Gaussian location model.
-- source:
--   The finite-dimensional Cameron-Martin formula; R. H. Cameron and W. T. Martin, Transformations of Wiener integrals under translations, Ann. of Math. 45 (1944), 386-396. Textbook form as the exponential-family representation of the Gaussian location model: E. L. Lehmann and G. Casella, Theory of Point Estimation, 2nd ed., Springer, 1998, Section 1.5, Example 5.5.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

theorem Statistics.gaussianReal_shift (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h : ℝ) :
    gaussianReal (m + h) v
      = (gaussianReal m v).withDensity
          (fun r => ENNReal.ofReal (rexp (h * (r - m) / v - h ^ 2 / (2 * v)))) := by sorry
