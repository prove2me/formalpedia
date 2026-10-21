-- Prove2me | Theorems.Thm_YeIPA_Center_primal_newton_quadratic
-- name    : YeIPA.Center.primal_newton_quadratic
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:02.845047+00:00
-- url     : https://prove2.me/theorems/8b3c309e-6b45-4c1c-b3c1-e150ff2a09f6
-- title:
--   Corollary 3.8 — the primal Newton step keeps $x^+>0$, $Ax^+=0$ and squares $\eta_p$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$ with $n>m$, let $c\in\mathbb R^n$, and suppose $\Omega=\{y: c-A^Ty\ge0\}$ is bounded with nonempty interior. Let $x$ be an interior point of $\mathcal X_\Omega=\{x: Ax=0,\ x\ge0\}$ (so $Ax=0$, $x>0$) with
--   $$\eta_p(x)=\|(I-XA^T(AX^2A^T)^{-1}AX)(Xc-e)\|<1 .$$
--   Take the primal Newton step $x^+=x+d_x$ with
--   $$d_x=-X(I-XA^T(AX^2A^T)^{-1}AX)(Xc-e).$$
--   Then
--   $$x^+>0,\qquad Ax^+=0,\qquad \eta_p(x^+)\le\eta_p(x)^2 .$$
--
--   This is the primal counterpart of Theorem 3.3: the primal Newton procedure converges quadratically to the primal potential minimizer once $\eta_p<1$. The book leaves its proof as an exercise.
--
--   **Formalization Note** The standing assumptions (rank $A=m$, $n>m$, $\Omega$ bounded with nonempty interior; pp. 48, 81) are explicit hypotheses. The Euclidean norm is written out.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 95, Corollary 3.8 (step (3.13))

import Mathlib
import Definitions.Def_YeIPA_Center_AnalyticCenter

open Matrix

namespace YeIPA.Center

/-- Corollary 3.8 (Ye 1997, p. 95). Under the standing assumptions (pp. 48, 81), let `x` be an
interior point of `X_Ω` with `η_p(x) < 1`, and let `x⁺ = x + d_x` with the primal Newton
direction `d_x = −X(I − XAᵀ(AX²Aᵀ)⁻¹AX)(Xc − e)` of (3.13). Then `x⁺ > 0`, `Ax⁺ = 0` and
`η_p(x⁺) ≤ η_p(x)²`. -/
theorem primal_newton_quadratic {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (hA : StandingAssumptions A c) (x : Fin n → ℝ) (hx : IsPrimalInterior A x)
    (hη : etaP A c x < 1) :
    (∀ j, 0 < primalNewtonStep A c x j) ∧ A *ᵥ primalNewtonStep A c x = 0 ∧
      etaP A c (primalNewtonStep A c x) ≤ etaP A c x ^ 2 := by sorry

end YeIPA.Center
