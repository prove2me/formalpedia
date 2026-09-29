-- Prove2me | Theorems.Thm_MarkovChainCLT_alpha_cov_bound_of_moment
-- name    : MarkovChainCLT.alpha_cov_bound_of_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-04T23:29:28.289468+00:00
-- url     : https://prove2.me/theorems/cfa3d02d-93f7-4cce-af73-88e2159d3bb3
-- title:
--   Ibragimov covariance bound from $\alpha$-mixing and $2+\delta$ moments
-- statement:
--   Ibragimov covariance inequality, existential-constant form.
--
--   Let $Y_0,Y_1,\dots$ be centered strictly stationary real random variables on a probability space, with $E|Y_0|^{2+\delta}<\infty$ for some $\delta>0$. Then there is a constant $C\ge 0$ (depending on the $(2+\delta)$-moment) such that for every lag $k\ge 0$,
--
--   $$
--   |E[Y_0Y_{k+1}]|\le C\,\alpha(k+1)^{\delta/(2+\delta)},
--   $$
--
--   where $\alpha$ is the strong mixing coefficient. This is the Davydov-Ibragimov covariance control behind Ibragimov-Linnik Theorem 18.5.3: truncation at a level balancing the $L^1$, $L^2$ and tail pieces against $\alpha$ via the covariance bound for bounded variables. Isolating it with an existential constant keeps the comparison-test application clean.
--
--   **Formalization Note** $\alpha$ is `alphaMixingCoef`; the power is a real power of a nonnegative real (junk $0$ when unbounded, as in the mission).
-- source:
--   Ibragimov 1962; Ibragimov-Linnik 1971 Theorem 18.5.3; Davydov covariance inequality, cf. Hall-Heyde Martingale Limit Theory Ch. 2; Jones 2004 Sec 4 Thm 5(ii) route

import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory

theorem MarkovChainCLT.alpha_cov_bound_of_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (hcent : ∫ ω, Y 0 ω ∂P = 0) (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, |∫ ω, Y 0 ω * Y (k + 1) ω ∂P| ≤ C * alphaMixingCoef P Y (k + 1) ^ (δ / (2 + δ)) := by sorry
