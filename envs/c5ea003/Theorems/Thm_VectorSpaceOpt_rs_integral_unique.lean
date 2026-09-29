-- Prove2me | Theorems.Thm_VectorSpaceOpt_rs_integral_unique
-- name    : VectorSpaceOpt.rs_integral_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T03:16:01.941436+00:00
-- url     : https://prove2.me/theorems/bf768a6f-e87d-4481-84ba-16efdcc57928
-- title:
--   Uniqueness of the Riemann--Stieltjes integral
-- statement:
--   The Riemann–Stieltjes integral is unique when it exists: if both $I$ and $J$ satisfy the defining approximation property
--
--   $$\forall \varepsilon>0\ \exists \delta>0:\quad \Bigl|\sum_i x(\xi_i)\bigl(v(t_{i+1})-v(t_i)\bigr)-I\Bigr|\le\varepsilon$$
--
--   for every tagged partition of $[a,b]$ of mesh below $\delta$, then $I=J$.
--
--   The point is that the family of tagged partitions of mesh below any given $\delta>0$ is nonempty — uniform partitions with enough pieces qualify — so the two approximation statements can be tested against a common partition, forcing $|I-J|\le 2\varepsilon$ for every $\varepsilon>0$. No regularity of the integrand $x$ or the integrator $v$ is needed; the hypothesis $a\le b$ is only what makes the uniform partitions exist.
--
--   This is the basic well-definedness fact that lets one speak of *the* integral $\int_a^b x\,dv$ and turn the relation `VectorSpaceOpt_is_rs_integral` into a function.
-- source:
--   D. G. Luenberger, Optimization by Vector Space Methods, Wiley 1969, §5.5, pp. 113-115 (Riesz representation for C[a,b]); the Riemann-Stieltjes facts are the standard ones, e.g. T. M. Apostol, Mathematical Analysis, 2nd ed., Ch. 7, Theorems 7.19 and 7.27.

import Mathlib
import Definitions.Def_VectorSpaceOpt_bv_stieltjes

namespace VectorSpaceOpt

theorem rs_integral_unique (a b : ℝ) (hab : a ≤ b) (x v : ℝ → ℝ) (I J : ℝ)
    (hI : VectorSpaceOpt_is_rs_integral x v a b I)
    (hJ : VectorSpaceOpt_is_rs_integral x v a b J) :
    I = J := by sorry

end VectorSpaceOpt
