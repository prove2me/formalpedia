-- Prove2me | Theorems.Thm_dirichlet_series_all_derivative_truncation_error_bound
-- name    : dirichlet_series_all_derivative_truncation_error_bound
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T04:51:37.051567+00:00
-- url     : https://prove2.me/theorems/3df26da7-d263-41e4-bcbe-662f22fd2485
-- title:
--   Explicit truncation bounds for every Dirichlet-series derivative
-- statement:
--   Let $f:\mathbb N\to\mathbb C$ satisfy $|M(N)|\le CN^r$ for all $N\ge1$, where $M(N)=\sum_{n=1}^Nf(n)$ and $r,C\ge0$. Let $F(s)=s\int_1^\infty M(\lfloor t\rfloor)t^{-s-1}\,dt$. Write $\sigma=\operatorname{Re}s$, and choose $0<\delta<\sigma-r$. For every integer $j\ge0$ and $N\ge1$,
--
--   $$\left|F^{(j)}(s)-\sum_{n=1}^N\frac{f(n)(-\log n)^j}{n^s}\right|
--   \le\frac{j!}{\delta^j}C\left(1+\frac{|s|+\delta}{\sigma-\delta-r}\right)N^{r-\sigma+\delta}.$$
--
--   This supplies a computable approximation error at every derivative order under a signed partial-sum bound. No absolute convergence of the original series and no zero-index normalization are assumed. The positive radius is strictly smaller than the distance to the convergence boundary.
-- source:
--   Derived Cauchy-estimate corollary. Pinned Mathlib https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/Liouville.lean#L44, Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le, combined with the finite Abel identity https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/AbelSummation.lean#L229, sum_mul_eq_sub_integral_mul₀'. The displayed constant is derived here, not quoted as a verbatim source theorem.

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
open MeasureTheory
open scoped Topology

theorem dirichlet_series_all_derivative_truncation_error_bound
    (f : ℕ → ℂ) {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ C * (N : ℝ) ^ r)
    {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδgap : δ < s.re - r)
    {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    ‖iteratedDeriv j (fun z : ℂ =>
        z * mellin (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) (-z)) s -
      (∑ n ∈ Finset.Icc 1 N, f n * (-Complex.log (n : ℂ)) ^ j / (n : ℂ) ^ s)‖ ≤
      (j.factorial : ℝ) / δ ^ j * C *
        (1 + (‖s‖ + δ) / (s.re - δ - r)) * (N : ℝ) ^ (r - s.re + δ) := by sorry
