-- Prove2me | Theorems.Thm_WirtingerFlow_hessian_quadratic_form_bounds
-- name    : WirtingerFlow.hessian_quadratic_form_bounds
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T21:25:22.455359+00:00
-- url     : https://prove2.me/theorems/77551501-7079-4843-a098-33a54df9862e
-- title:
--   Corollary 7.5: two-sided bounds on the Hessian quadratic form
-- statement:
--   Let $a_1,\dots,a_m\in\mathbb{C}^n$ ($m\ge1$) be any sampling vectors, let $x\in\mathbb{C}^n$ with $\|x\|=1$, let $f$ use the data $y_r=|a_r^*x|^2$, and suppose
--
--   $$\big\|\nabla^2f(x)-\mathbb E[\nabla^2f(x)]\big\|\le\delta,$$
--
--   where $\mathbb E[\nabla^2f(x)]$ denotes the matrix of Lemma 7.1. Then for every $h\in\mathbb{C}^n$ with $\|h\|=1$,
--
--   $$\frac1m\sum_{r=1}^m\operatorname{Re}\big(h^*a_ra_r^*x\big)^2=\frac14\begin{bmatrix}h\\\bar h\end{bmatrix}^*\nabla^2f(x)\begin{bmatrix}h\\\bar h\end{bmatrix},$$
--
--   and this quantity lies between
--
--   $$\Big(\frac12\|h\|^2+\frac32\operatorname{Re}(x^*h)^2-\frac12\operatorname{Im}(x^*h)^2\Big)\mp\frac\delta2.$$
--
--   **Formalization Note** The printed identity has a superfluous $\sum_{r=1}^m$ in front of the quadratic form, which does not depend on $r$. The statement uses the quadratic form alone, which is what the proof computes. The corollary is deterministic, and the matrix $\mathbb E[\nabla^2f(x)]$ is written out explicitly as in Lemma 7.1.
-- source:
--   Candès, Li and Soltanolkotabi, Phase Retrieval via Wirtinger Flow: Theory and Algorithms, arXiv:1407.1065v3 (2015), Section 7.3, Corollary 7.5, p. 21; proof in Appendix A.5, p. 40

import Mathlib
import Definitions.Def_WirtingerFlow_Basic

open MeasureTheory ProbabilityTheory Complex Matrix

namespace WirtingerFlow

theorem hessian_quadratic_form_bounds {R : Type*} [Fintype R] [Nonempty R] {n : ℕ}
    (a : R → Sig n) (x : Sig n) (hx : ‖x‖ = 1) (δ : ℝ)
    (hδ : opNorm (hess a (meas a x) x - expHess x) ≤ δ) (h : Sig n) (hh : ‖h‖ = 1) :
    (((1 / (Fintype.card R : ℝ) * ∑ r, ((inner ℂ h (a r) * inner ℂ (a r) x).re) ^ 2 : ℝ) : ℂ) =
      1 / 4 * (star (stack h) ⬝ᵥ (hess a (meas a x) x *ᵥ stack h))) ∧
    1 / (Fintype.card R : ℝ) * ∑ r, ((inner ℂ h (a r) * inner ℂ (a r) x).re) ^ 2 ≤
      (1 / 2 * ‖h‖ ^ 2 + 3 / 2 * (inner ℂ x h).re ^ 2 - 1 / 2 * (inner ℂ x h).im ^ 2) + δ / 2 ∧
    (1 / 2 * ‖h‖ ^ 2 + 3 / 2 * (inner ℂ x h).re ^ 2 - 1 / 2 * (inner ℂ x h).im ^ 2) - δ / 2 ≤
      1 / (Fintype.card R : ℝ) * ∑ r, ((inner ℂ h (a r) * inner ℂ (a r) x).re) ^ 2 := by sorry

end WirtingerFlow
