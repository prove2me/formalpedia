-- Prove2me | Theorems.Thm_ordered_dirichlet_series_locally_uniform_of_partial_sum_bound
-- name    : ordered_dirichlet_series_locally_uniform_of_partial_sum_bound
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T02:48:56.277785+00:00
-- url     : https://prove2.me/theorems/79e118e4-bd69-4185-b1af-7e10e711b44b
-- title:
--   Locally uniform Dirichlet-series convergence from signed partial-sum growth
-- statement:
--   Let $f:\mathbb N\to\mathbb C$ and $r\ge0$, and assume $M(N)=\sum_{n=1}^Nf(n)=O(N^r)$. Put $F(s)=s\int_1^\infty M(\lfloor t\rfloor)t^{-s-1}\,dt$. Then
--
--   $$\sum_{n=1}^Nf(n)n^{-s}\longrightarrow F(s)\quad\text{locally uniformly on }\operatorname{Re}s>r.$$
--
--   In particular the convergence is uniform on each compact subset of that half-plane. Uniformity on the entire unbounded half-plane is not asserted. This stronger mode of convergence supports holomorphic limit arguments and differentiation.
-- source:
--   Quantitative corollary proved from pinned Mathlib https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/AbelSummation.lean#L229, sum_mul_eq_sub_integral_mul₀', and https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean#L172, integral_Ioi_rpow_of_lt. The explicit resulting error bound is uniform on each set Re(s)>=sigma>r, |s|<=R.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
open MeasureTheory
open scoped Topology

theorem ordered_dirichlet_series_locally_uniform_of_partial_sum_bound
    (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)
      (fun N : ℕ => (N : ℝ) ^ r)) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)
      (fun s : ℂ => s * mellin (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) (-s))
      Filter.atTop {s : ℂ | r < s.re} := by sorry
