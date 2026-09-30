-- Prove2me | Theorems.Thm_dirichlet_boundary_convergence_and_error_of_log_squared_saving
-- name    : dirichlet_boundary_convergence_and_error_of_log_squared_saving
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T04:51:39.38356+00:00
-- url     : https://prove2.me/theorems/d26da3fa-c057-4cba-8f54-d45f1daf06b8
-- title:
--   Boundary Dirichlet convergence and explicit error from a logarithmic partial-sum saving
-- statement:
--   Let $f:\mathbb N\to\mathbb C$, $r>0$, $C\ge0$, and suppose
--
--   $$|M(N)|=\left|\sum_{n=1}^Nf(n)\right|\le\frac{CN^r}{(\log N)^2}\qquad(N\ge2).$$
--
--   At every point on the boundary $\operatorname{Re}s=r$, the ordered Dirichlet partial sums converge to the Mellin integral $F(s)=s\int_1^\infty M(\lfloor t\rfloor)t^{-s-1}\,dt$, and for $N\ge2$,
--
--   $$\left|F(s)-\sum_{n=1}^N f(n)n^{-s}\right|
--   \le\frac{4C}{(\log N)^2}+\frac{4C|s|}{\log N}.$$
--
--   Thus a logarithmic saving suffices for ordered convergence on the boundary itself. This does not assert analytic continuation through that boundary, absolute convergence of the Dirichlet series, or convergence of its differentiated series there. No such logarithmic Moebius bound is proved.
-- source:
--   Derived boundary Abel-summation criterion. Pinned Mathlib https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/AbelSummation.lean#L229, sum_mul_eq_sub_integral_mul₀'; https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean#L292, integrableOn_inv_div_log_sq_Ioi; and the exact tail integral https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean#L303, integral_inv_div_log_sq_Ioi. The factor 4 accounts for transferring the discrete logarithmic bound to the floor-summatory function; the displayed result is derived here.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
open MeasureTheory
open scoped Topology

theorem dirichlet_boundary_convergence_and_error_of_log_squared_saving
    (f : ℕ → ℂ) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 2 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤
        C * (N : ℝ) ^ r / (Real.log (N : ℝ)) ^ 2)
    {s : ℂ} (hs : s.re = r) :
    let F := fun z : ℂ =>
      z * mellin (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) (-z)
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)
      Filter.atTop (nhds (F s)) ∧
    ∀ N : ℕ, 2 ≤ N →
      ‖F s - (∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)‖ ≤
        4 * C / (Real.log (N : ℝ)) ^ 2 + 4 * C * ‖s‖ / Real.log (N : ℝ) := by sorry
