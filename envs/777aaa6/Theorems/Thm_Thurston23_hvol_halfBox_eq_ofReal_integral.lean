-- Prove2me | Theorems.Thm_Thurston23_hvol_halfBox_eq_ofReal_integral
-- name    : Thurston23.hvol_halfBox_eq_ofReal_integral
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-13T16:29:23.714609+00:00
-- url     : https://prove2.me/theorems/4efc3e38-ceea-44d0-810d-dbcc586d27c4
-- title:
--   The volume of the half box is $-\int_0^{\pi/4} \log\bigl(1 - \tfrac{1}{4\cos^2\theta}\bigr)\,d\theta$
-- statement:
--   The hyperbolic volume $\int_B t^{-3}\,dx\,dy\,dt$ of the half box $B = \{|x| \le \tfrac12,\ 0 \le y \le \tfrac12,\ x^2+y^2+t^2 \ge 1\}$ equals
--
--   $$-\int_0^{\pi/4} \log\Bigl(1 - \frac{1}{4\cos^2\theta}\Bigr)\,d\theta,$$
--
--   stated in $[0, \infty]$ through `ENNReal.ofReal`. The height integral $\int_a^\infty t^{-3}\,dt = 1/(2a^2)$ reduces the volume to the plane integral $\int_D dx\,dy / (2(1 - x^2 - y^2))$ over the base $D = [-\tfrac12, \tfrac12] \times [0, \tfrac12]$; in polar coordinates a ray at angle $\theta \in [0, \pi)$ leaves $D$ at $r = 1/(2\max(|\cos\theta|, \sin\theta))$, the radial integral is $-\tfrac14 \log(1 - r^2)$, and the angular integral over $[0, \pi]$ folds by $\theta \mapsto \pi - \theta$ and $\theta \mapsto \pi/2 - \theta$ onto $[0, \pi/4]$, where the bound is $1/(2\cos\theta)$. The integral evaluates to $-G/3$, $G$ Catalan's constant (a separate, Mathlib-only statement), which is Humbert's formula for $\mathbb{Q}(i)$.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). G. Humbert, Sur la mesure des classes d'Hermite de discriminant donné dans un corps quadratique imaginaire, C. R. Acad. Sci. Paris 169 (1919), 448-454. Formalisation: https://github.com/t4v1/thurston23/blob/58bb3fd/Thurston23.lean#L3744-L3751 (section Polar).

import Definitions.Def_Thurston23_picard

namespace Thurston23

open MeasureTheory

theorem hvol_halfBox_eq_ofReal_integral :
    hvol halfBox = ENNReal.ofReal
      (-∫ θ in (0:ℝ)..Real.pi / 4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))) := by
  sorry

end Thurston23
