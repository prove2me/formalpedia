-- Prove2me | Theorems.Thm_MarkovChainCLT_abs_exp_variance_sub_le_of_tendstoInDistribution
-- name    : MarkovChainCLT.abs_exp_variance_sub_le_of_tendstoInDistribution
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:07:04.850968+00:00
-- url     : https://prove2.me/theorems/9909bd99-7e19-4f01-a3a0-405fda4593f5
-- title:
--   Gaussian limits of L¹-close sequences have close variances
-- statement:
--   **Two sequences that stay $L^1$-close cannot have Gaussian limits with distant variances.** Suppose $Y_n \Rightarrow N(0,v)$ and $Z_n \Rightarrow N(0,w)$, and that $\mathbb E|Y_n - Z_n| \le \varepsilon$ for every $n$. Then
--   $$\bigl| e^{-v/2} - e^{-w/2} \bigr| \;\le\; \varepsilon .$$
--
--   **Discussion.** Weak convergence is not metrized by $L^1$ distance, so no bound on $|v-w|$ can be read off directly; but a *single* bounded Lipschitz test function is enough. Take $\varphi = \cos$: it is $1$-Lipschitz and bounded, so
--   $$\bigl| \mathbb E\cos Y_n - \mathbb E\cos Z_n \bigr| \le \mathbb E\bigl|\cos Y_n - \cos Z_n\bigr| \le \mathbb E|Y_n - Z_n| \le \varepsilon,$$
--   and both sides converge, by the portmanteau theorem, to the corresponding Gaussian integrals. Since $\int\cos\,dN(0,u) = e^{-u/2}$, the claim follows by passing to the limit in a non-strict inequality.
--
--   **Where this is used.** In the Markov chain central limit theorem for an $L^2$ observable $f$ one truncates $f$ at level $K$, applies the bounded-observable theorem to obtain $S_n(f_K)/\sqrt n \Rightarrow N(0,v_K)$, and needs $(v_K)$ to converge. The $O(n)$ variance bound for partial sums gives $\mathbb E\bigl| S_n(f_K)/\sqrt n - S_n(f_L)/\sqrt n \bigr| \le 2\sqrt{N}\,\|f_K - f_L\|_{L^2(\pi)}$ uniformly in $n$, so this lemma makes $\bigl(e^{-v_K/2}\bigr)$ Cauchy; together with a uniform upper bound on $v_K$ the map $u \mapsto e^{-u/2}$ is bi-Lipschitz on the relevant range, so $(v_K)$ itself is Cauchy.
--
--   **Proof.** Package $\cos$ as a bounded continuous function, use the portmanteau characterisation of weak convergence contained in `TendstoInDistribution` to get $\mathbb E\cos Y_n \to \int\cos\,dN(0,v) = e^{-v/2}$ and likewise for $Z$; bound $\bigl|\mathbb E\cos Y_n - \mathbb E\cos Z_n\bigr|$ by $\varepsilon$ using linearity, the triangle inequality for integrals, monotonicity, and the Lipschitz bound for $\cos$; then take limits.
-- source:
--   P. Billingsley, Convergence of Probability Measures, 2nd ed., Wiley 1999, Section 1 (the bounded-Lipschitz metric); G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320; I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971.

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.abs_exp_variance_sub_le_of_tendstoInDistribution {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y Z : ℕ → Ω → ℝ) (v w : ℝ≥0) (ε : ℝ)
    (hY : ∀ n, Measurable (Y n)) (hZ : ∀ n, Measurable (Z n))
    (hcY : TendstoInDistribution Y atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 v))
    (hcZ : TendstoInDistribution Z atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 w))
    (hint : ∀ n, Integrable (fun ω => |Y n ω - Z n ω|) μ)
    (hdiff : ∀ n, ∫ ω, |Y n ω - Z n ω| ∂μ ≤ ε) :
    |Real.exp (-(v : ℝ) / 2) - Real.exp (-(w : ℝ) / 2)| ≤ ε := by sorry
