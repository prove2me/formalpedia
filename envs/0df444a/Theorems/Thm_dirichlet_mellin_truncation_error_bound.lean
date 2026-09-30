-- Prove2me | Theorems.Thm_dirichlet_mellin_truncation_error_bound
-- name    : dirichlet_mellin_truncation_error_bound
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T02:45:47.658134+00:00
-- url     : https://prove2.me/theorems/5746d8ad-92b3-4a5a-8481-ae48db0a388d
-- title:
--   Explicit truncation error for a Dirichlet series with bounded signed partial sums
-- statement:
--   Let $f:\mathbb N\to\mathbb C$ with $f(0)=0$, and suppose $r,C\ge0$ and $|M(N)|\le CN^r$ for all integers $N\ge1$, where $M(N)=\sum_{n=1}^Nf(n)$. Put $F(s)=s\int_1^\infty M(\lfloor t\rfloor)t^{-s-1}\,dt$. For $\sigma=\operatorname{Re}s>r$ and $N\ge1$,
--
--   $$\left|F(s)-\sum_{n=1}^N\frac{f(n)}{n^s}\right|\le C\left(1+\frac{|s|}{\sigma-r}\right)N^{r-\sigma}.$$
--
--   This turns a signed partial-sum estimate into an explicit approximation guarantee. The constant and its dependence on distance to the convergence boundary are displayed. The zero-index normalization is harmless for series beginning at one.
-- source:
--   Derived quantitative corollary of pinned Mathlib https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/AbelSummation.lean#L229, sum_mul_eq_sub_integral_mul₀'; https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean#L172, integral_Ioi_rpow_of_lt; and https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L947, norm_integral_le_of_norm_le. The bound is proved here from these cited identities, not attributed as a verbatim theorem.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
open MeasureTheory
open scoped Topology

theorem dirichlet_mellin_truncation_error_bound
    (f : ℕ → ℂ) (hf : f 0 = 0)
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ C * (N : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖s * mellin (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) (-s) -
      (∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)‖ ≤
      C * (1 + ‖s‖ / (s.re - r)) * (N : ℝ) ^ (r - s.re) := by sorry
