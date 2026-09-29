-- Prove2me | Theorems.Thm_MarkovChainCLT_exists_truncation_tail_variance_le_of_exp_alpha_of_log_moment
-- name    : MarkovChainCLT.exists_truncation_tail_variance_le_of_exp_alpha_of_log_moment
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T10:53:43.217311+00:00
-- url     : https://prove2.me/theorems/e5502a1c-e5f1-4dff-8499-bc0eb58380fc
-- title:
--   The truncated tail of a partial sum has uniformly small variance
-- statement:
--   Let $Y=(Y_i)_{i\ge0}$ be a measurable, centered, strictly stationary real sequence with exponentially decaying strong mixing coefficients, $\alpha(n)\le c\,a^{n}$ with $0\le a<1$, and with a finite log-weighted second moment $E\bigl[Y_0^2\log^+|Y_0|\bigr]<\infty$.
--
--   For a truncation level $T>0$ write $Y_i^{>T}=Y_i\mathbf 1\{|Y_i|>T\}-E\bigl[Y_0\mathbf 1\{|Y_0|>T\}\bigr]$ for the recentered high part of $Y_i$. Then the variance of the partial sums of the high parts is uniformly small once the level is high enough: for every $\varepsilon>0$ there is $T>0$ with
--
--   $$E\Bigl[\Bigl(\sum_{i<n}Y_i^{>T}\Bigr)^{2}\Bigr]\ \le\ \varepsilon\,n\qquad\text{for all }n .$$
--
--   The bound is uniform in $n$ after division by $n$, which is what makes the truncation error negligible relative to $E[S_n^2]\asymp\sigma^2n$. Expanding the square, the left-hand side is at most $n\bigl(E[(Y_0^{>T})^2]+2\sum_{k\ge1}\lvert E[Y_0^{>T}Y_k^{>T}]\rvert\bigr)$ by stationarity, so the assertion is that the bracket tends to $0$ as $T\to\infty$: the first term does so by dominated convergence, and the covariance series does so because the same geometric truncation scheme that makes $\sum_k|E[Y_0Y_k]|$ finite under the log moment applies to the high parts, whose log-weighted second moments vanish as $T\to\infty$.
-- source:
--   P. Doukhan, P. Massart and E. Rio, The functional central limit theorem for strongly mixing processes, Ann. Inst. H. Poincare Probab. Statist. 30 (1994) 63-82, Theorem 1 and its proof (control of the truncated tail); E. Rio, Covariance inequalities for strongly mixing processes, Ann. Inst. H. Poincare Probab. Statist. 29 (1993) 587-597, Theorem 1.1. This is the truncation step of Theorem 6 of G. L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.exists_truncation_tail_variance_le_of_exp_alpha_of_log_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ,
      ∫ ω, (∑ i ∈ Finset.range n,
        ((if T < |Y i ω| then Y i ω else 0)
          - ∫ ω', (if T < |Y 0 ω'| then Y 0 ω' else 0) ∂P)) ^ 2 ∂P ≤ ε * n := by sorry
