-- Prove2me | Theorems.Thm_MarkovChainCLT_memLp_two_of_integrable_rpow
-- name    : MarkovChainCLT.memLp_two_of_integrable_rpow
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:41:47.884827+00:00
-- url     : https://prove2.me/theorems/610dc8ff-af1a-4df7-945f-196bc404ae7e
-- title:
--   $L^{2+\delta}$-integrability implies $L^2$
-- statement:
--   A $(2+\delta)$-th absolute moment controls the second moment.
--
--   Let $Y$ be a real random variable on a probability space, a.e. strongly measurable, with $E|Y|^{2+\delta}<\infty$ for some $\delta>0$. Then $Y\in L^2$.
--
--   Indeed $|Y|^{2+\delta}$-integrability gives $Y\in L^{2+\delta}$ via $\int^-\|Y\|_e^{2+\delta}<\infty$, and $L^{2+\delta}\subseteq L^2$ on a finite measure by monotonicity of $L^p$ norms. The a.e. measurability hypothesis is load-bearing: integrability of $|Y|^{2+\delta}$ alone does not make $Y$ measurable.
--
--   **Formalization Note** Real powers throughout; $2$ is `(2:\mathbb R_{\ge 0\infty})` for `MemLp`.
-- source:
--   Standard L^p comparison on finite measures; MemLp.mono_exponent

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.memLp_two_of_integrable_rpow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (δ : ℝ) (hδ : 0 < δ) (hYm : AEStronglyMeasurable Y P) (hmom : Integrable (fun ω => |Y ω| ^ (2 + δ)) P) : MemLp Y 2 P := by sorry
