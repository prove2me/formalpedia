-- Prove2me | Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound
-- name    : nontrivial_zero_strip_of_moebius_summatory_power_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-10T19:17:25.02668+00:00
-- url     : https://prove2.me/theorems/e484efc7-3556-463f-a958-ba72037cc2af
-- title:
--   A Moebius partial-sum bound confines nontrivial zeta zeros to a symmetric strip
-- statement:
--   Let $r\ge0$, let $\mu$ be the Moebius function, and assume the signed partial sums
--
--   $$M(N)=\sum_{n\le N}\mu(n)$$
--
--   satisfy $M(N)=O(N^{r})$ as $N\to\infty$. Then every nontrivial zero $s$ of the Riemann zeta function, that is, every zero other than the trivial zeros $-2,-4,-6,\dots$ and the point $s=1$, satisfies
--
--   $$1-r\le\operatorname{Re}s\le r.$$
--
--   This is a quantitative conditional zero-location statement: a cancellation bound for the Mertens function of exponent $r$ confines the nontrivial zeros to the closed strip $1-r\le\operatorname{Re}s\le r$. It asserts nothing about the truth of the cancellation hypothesis itself. Its reuse value is that it converts arithmetic information about $\mu$ into analytic information about the zeros of $\zeta$.
--
--   **Formalization Note.** The trivial zeros are excluded by the hypothesis that $s$ is not of the form $-2(n+1)$ for a natural number $n$, and the point $s=1$ by $s\neq1$. The partial sums are embedded into the complex numbers, and the growth hypothesis is a Lean `IsBigO` statement along `atTop` against $N\mapsto N^{r}$. This is the statement `nontrivial_zero_strip_of_moebius_summatory_power_bound`, recreated verbatim in the Mathlib `777aaa6` environment so that theorems of that environment can cite it; it is already proved in the default environment.
-- source:
--   Derived corollary of signed Abel-Mellin continuation and the zeta functional equation. Pinned Mathlib (env 777aaa6): https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/Analysis/MellinTransform.lean , mellin_differentiableAt_of_isBigO_rpow; https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/NumberTheory/LSeries/RiemannZeta.lean , completedRiemannZeta_one_sub; https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/NumberTheory/LSeries/Nonvanishing.lean , riemannZeta_ne_zero_of_one_le_re. Context: E. C. Titchmarsh, The Theory of the Riemann Zeta-function, second edition revised by D. R. Heath-Brown (1986), Section 14.25(A), p. 369, and the analytic-continuation paragraph preceding 14.25(B), p. 370. https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf .

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
open MeasureTheory
open scoped Topology

theorem nontrivial_zero_strip_of_moebius_summatory_power_bound
    {r : ℝ} (hr : 0 ≤ r)
    (hM : Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
      (fun N : ℕ => (N : ℝ) ^ r))
    {s : ℂ} (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) (h1 : s ≠ 1) :
    1 - r ≤ s.re ∧ s.re ≤ r := by sorry
