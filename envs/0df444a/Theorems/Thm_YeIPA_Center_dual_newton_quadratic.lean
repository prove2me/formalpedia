-- Prove2me | Theorems.Thm_YeIPA_Center_dual_newton_quadratic
-- name    : YeIPA.Center.dual_newton_quadratic
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:54.155609+00:00
-- url     : https://prove2.me/theorems/21d8f060-ba5d-4b76-a462-0441f6f39a0e
-- title:
--   Theorem 3.3 — the dual Newton step keeps $s^+>0$ and squares $\eta_d$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$ with $n>m$, let $c\in\mathbb R^n$, and suppose $\Omega=\{y: c-A^Ty\ge0\}$ is bounded with nonempty interior. Let $(y,s)$ be an interior point of $\Omega$ with
--   $$\eta_d(s)=\|S^{-1}A^T(AS^{-2}A^T)^{-1}AS^{-1}e\|<1 .$$
--   Take the dual Newton step $s^+=s+d_s$ with
--   $$d_s=A^T(AS^{-2}A^T)^{-1}AS^{-1}e .$$
--   Then
--   $$s^+>0\qquad\text{and}\qquad \eta_d(s^+)\le\eta_d(s)^2 .$$
--
--   Since $s^+=c-A^T(y+d_y)$ with $d_y=-(AS^{-2}A^T)^{-1}AS^{-1}e$, the new point is again an interior point of $\Omega$, and the dual Newton procedure converges quadratically to the analytic center once $\eta_d<1$.
--
--   **Formalization Note** The standing assumptions (rank $A=m$, $n>m$, $\Omega$ bounded with nonempty interior; pp. 48, 81) are explicit hypotheses. $s^+>0$ means every coordinate is positive. The Euclidean norm is written out.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 88, Theorem 3.3 (step (3.9))

import Mathlib
import Definitions.Def_YeIPA_Center_AnalyticCenter

open Matrix

namespace YeIPA.Center

/-- Theorem 3.3 (Ye 1997, p. 88). Under the standing assumptions (pp. 48, 81), let `(y, s)` be
an interior point of Ω with `η_d(s) < 1`, and let `s⁺ = s + d_s` with the dual Newton
direction `d_s = Aᵀ(AS⁻²Aᵀ)⁻¹AS⁻¹e` of (3.9). Then `s⁺ > 0` and `η_d(s⁺) ≤ η_d(s)²`. -/
theorem dual_newton_quadratic {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (hA : StandingAssumptions A c) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (hs : IsDualInterior A c y s) (hη : etaD A s < 1) :
    (∀ j, 0 < dualNewtonStep A s j) ∧ etaD A (dualNewtonStep A s) ≤ etaD A s ^ 2 := by sorry

end YeIPA.Center
