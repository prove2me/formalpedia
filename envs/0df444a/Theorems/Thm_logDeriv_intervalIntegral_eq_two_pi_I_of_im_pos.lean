-- Prove2me | Theorems.Thm_logDeriv_intervalIntegral_eq_two_pi_I_of_im_pos
-- name    : logDeriv_intervalIntegral_eq_two_pi_I_of_im_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T19:02:19.658921+00:00
-- url     : https://prove2.me/theorems/3c30ea5f-58d0-4e44-b038-b5380b012e86
-- title:
--   A closed loop with increasing argument that meets its initial ray only at the ends winds once
-- statement:
--   Let $c:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be $C^1$ with $c(1)=c(0)$. Suppose the argument strictly increases, $\operatorname{Im}(c'/c)>0$, and for $0<t<1$ the point $c(t)$ is never a positive multiple of $c(0)$. Then
--   $$\int_0^1\frac{c'(s)}{c(s)}\,ds=2\pi i .$$
--   The total change of argument is $2\pi k$ with $k\ge1$. If $k\ge2$, the argument passes $2\pi$ at some $t\in(0,1)$, and there $c(t)\in\mathbb{R}_{>0}\,c(0)$.
-- source:
--   Standard winding-number calculus for C^1 loops in C \ {0}; used for the conormal winding of a disk-like global surface of section in Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 1.7 (via Hryniewicz, Trans. AMS 364 (2012), Prop. 2.1).

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs

open scoped ContDiff

theorem logDeriv_intervalIntegral_eq_two_pi_I_of_im_pos {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (hper : c 1 = c 0)
    (hpos : ∀ t, 0 < (c' t / c t).im)
    (hray : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ l : ℝ, 0 < l → c t ≠ (l : ℂ) * c 0) :
    ∫ s in (0 : ℝ)..1, c' s / c s = 2 * Real.pi * Complex.I := by sorry
