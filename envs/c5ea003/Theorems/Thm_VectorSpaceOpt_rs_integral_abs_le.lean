-- Prove2me | Theorems.Thm_VectorSpaceOpt_rs_integral_abs_le
-- name    : VectorSpaceOpt.rs_integral_abs_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T03:16:14.023384+00:00
-- url     : https://prove2.me/theorems/922f60cd-300a-434d-81c1-f4afb31986b3
-- title:
--   $\left|\int_a^b x\,dv\right| \le \|x\|_\infty\, \mathrm{T.V.}(v)$
-- statement:
--   Let $v$ be of bounded variation on $[a,b]$ and let $x$ be bounded by $C$ on $[a,b]$. If the Riemann–Stieltjes integral $I=\int_a^b x\,dv$ exists, then
--
--   $$\left|\int_a^b x\,dv\right|\ \le\ C\cdot \mathrm{T.V.}(v),$$
--
--   where $\mathrm{T.V.}(v)$ is the total variation of $v$ on $[a,b]$.
--
--   Every Riemann–Stieltjes sum obeys the bound termwise, $\bigl|\sum_i x(\xi_i)(v(t_{i+1})-v(t_i))\bigr|\le C\sum_i|v(t_{i+1})-v(t_i)|\le C\cdot\mathrm{T.V.}(v)$, and the integral is a limit of such sums.
--
--   This is the estimate that makes integration against a fixed function of bounded variation a **bounded** linear functional on $C[a,b]$, with norm at most $\mathrm{T.V.}(v)$ — one half of the Riesz representation theorem for $C[a,b]$.
-- source:
--   D. G. Luenberger, Optimization by Vector Space Methods, Wiley 1969, §5.5, pp. 113-115 (Riesz representation for C[a,b]); the Riemann-Stieltjes facts are the standard ones, e.g. T. M. Apostol, Mathematical Analysis, 2nd ed., Ch. 7, Theorems 7.19 and 7.27.

import Mathlib
import Definitions.Def_VectorSpaceOpt_bv_stieltjes

namespace VectorSpaceOpt

theorem rs_integral_abs_le (a b : ℝ) (hab : a ≤ b) (x v : ℝ → ℝ) (C I : ℝ)
    (hv : BoundedVariationOn v (Set.Icc a b)) (hC : 0 ≤ C)
    (hxC : ∀ p ∈ Set.Icc a b, |x p| ≤ C)
    (hI : VectorSpaceOpt_is_rs_integral x v a b I) :
    |I| ≤ C * VectorSpaceOpt_total_variation v a b := by sorry

end VectorSpaceOpt
