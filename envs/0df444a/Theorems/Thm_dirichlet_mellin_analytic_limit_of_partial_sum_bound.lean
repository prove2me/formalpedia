-- Prove2me | Theorems.Thm_dirichlet_mellin_analytic_limit_of_partial_sum_bound
-- name    : dirichlet_mellin_analytic_limit_of_partial_sum_bound
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T02:45:48.194279+00:00
-- url     : https://prove2.me/theorems/557f3b52-774c-43a5-85ec-93534ddbe38c
-- title:
--   Analytic ordered Dirichlet-series limit from a signed partial-sum bound
-- statement:
--   Let $f:\mathbb N\to\mathbb C$, $r\ge0$, and $M(N)=\sum_{n=1}^N f(n)=O(N^r)$. Define $M(t)=M(\lfloor t\rfloor)$ and
--
--   $$F(s)=s\int_1^\infty M(t)t^{-s-1}\,dt.$$
--
--   Then $F$ is analytic on $\operatorname{Re}s>r$, and for every point in this half-plane,
--
--   $$\lim_{N\to\infty}\sum_{n=1}^N\frac{f(n)}{n^s}=F(s).$$
--
--   The hypothesis bounds the signed sums, not the sums of absolute values. The conclusion concerns the displayed ordering of partial sums and does not assert absolute convergence. This is a reusable analytic continuation mechanism for cancellation-sensitive Dirichlet series.
-- source:
--   Derived specialization of pinned Mathlib https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/AbelSummation.lean#L300, tendsto_sum_mul_atTop_nhds_one_sub_integral₀, and https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/MellinTransform.lean#L401, mellin_differentiableAt_of_isBigO_rpow. The cutoff below 1 turns the Mellin transform into the displayed improper integral.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.CauchyIntegral
open MeasureTheory
open scoped Topology

theorem dirichlet_mellin_analytic_limit_of_partial_sum_bound
    (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)
      (fun N : ℕ => (N : ℝ) ^ r)) :
    let F := fun s : ℂ => s * mellin (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) (-s)
    AnalyticOnNhd ℂ F {s : ℂ | r < s.re} ∧
      ∀ s : ℂ, r < s.re →
        Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)
          Filter.atTop (nhds (F s)) := by sorry
