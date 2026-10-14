-- Prove2me | Theorems.Thm_Thurston23_hvol_eisBox_eq_ofReal_integral
-- name    : Thurston23.hvol_eisBox_eq_ofReal_integral
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-14T16:24:01.379872+00:00
-- url     : https://prove2.me/theorems/8bc7c44b-d64a-4ea0-9aea-e7fc42cae181
-- title:
--   The volume of the box over the rhombus is $-\int_0^{\pi/6} \log\bigl(1 - \tfrac{1}{4\cos^2\theta}\bigr)\,d\theta$
-- statement:
--   The hyperbolic volume $\int_B t^{-3}\,dx\,dy\,dt$ of the box $B = \{0 \le x \le \tfrac12,\ 0 \le x + \sqrt3\,y \le 1,\ x^2+y^2+t^2 \ge 1\}$ equals
--
--   $$-\int_0^{\pi/6} \log\Bigl(1 - \frac{1}{4\cos^2\theta}\Bigr)\,d\theta,$$
--
--   stated in $[0,\infty]$ through `ENNReal.ofReal`. The height integral reduces the volume to $\int dx\,dy/(2(1 - x^2 - y^2))$ over the rhombus; in polar coordinates the rhombus is $\theta \in [-\pi/6, \pi/2]$, $r \le 1/(2\max(\cos\theta, \cos(\theta - \pi/3)))$, the radial integral is $-\tfrac14\log(1 - r^2)$, and the angle folds onto $[0, \pi/6]$. The integral evaluates to $-\sqrt3\,L(2,\chi_{-3})/8$ (a separate, Mathlib-only statement), which is Humbert's formula for $\mathbb{Q}(\sqrt{-3})$.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). J. Elstrodt, F. Grunewald, J. Mennicke, Groups Acting on Hyperbolic Space, Springer 1998, Chapter 7 (Bianchi groups and Humbert's formula). Formalisation: https://github.com/t4v1/thurston23/blob/main/Thurston23Eisenstein.lean (hvol_eisBox_eq_ofReal_integral).

import Definitions.Def_Thurston23_eisenstein

namespace Thurston23

open MeasureTheory

theorem hvol_eisBox_eq_ofReal_integral :
    hvol eisBox = ENNReal.ofReal
      (-∫ θ in (0:ℝ)..Real.pi / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))) := by
  sorry

end Thurston23
