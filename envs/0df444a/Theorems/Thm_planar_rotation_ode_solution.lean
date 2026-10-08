-- Prove2me | Theorems.Thm_planar_rotation_ode_solution
-- name    : planar_rotation_ode_solution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T16:15:11.824174+00:00
-- url     : https://prove2.me/theorems/596c3ccc-f7df-4ba3-b119-33be8c435138
-- title:
--   Solutions of $a'=-\omega b,\ b'=\omega a$ are rotations
-- statement:
--   Let $\omega\in\mathbb R$ and let $a,b:\mathbb R\to\mathbb R$ be differentiable with $a'(t)=-\omega\,b(t)$ and $b'(t)=\omega\,a(t)$ for all $t$. Then $(a,b)$ is the rotation of its initial value:
--   $$a(t)=\cos(\omega t)\,a(0)-\sin(\omega t)\,b(0),\qquad b(t)=\sin(\omega t)\,a(0)+\cos(\omega t)\,b(0).$$
--   Proof idea: $R(-\omega t)\,(a(t),b(t))$ has zero derivative, hence is constant.
-- source:
--   Uniqueness for the linear ODE $z'=i\omega z$ (standard); used for the explicit ellipsoid flow in Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), https://arxiv.org/abs/1105.2077, p. 3 (ellipsoid example after Theorem 1.7)

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

theorem planar_rotation_ode_solution (a b : ℝ → ℝ) (w : ℝ)
    (ha : ∀ t, HasDerivAt a (-(w * b t)) t) (hb : ∀ t, HasDerivAt b (w * a t) t) (t : ℝ) :
    a t = Real.cos (w * t) * a 0 - Real.sin (w * t) * b 0 ∧
      b t = Real.sin (w * t) * a 0 + Real.cos (w * t) * b 0 := by sorry
