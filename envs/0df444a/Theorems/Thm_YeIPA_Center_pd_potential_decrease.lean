-- Prove2me | Theorems.Thm_YeIPA_Center_pd_potential_decrease
-- name    : YeIPA.Center.pd_potential_decrease
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:00.212412+00:00
-- url     : https://prove2.me/theorems/49d34e25-d3ff-4cfa-965b-e5f01f4fc600
-- title:
--   Lemma 3.12 — a damped primal-dual Newton step lowers $\psi_n$ by $\alpha\sqrt{\min(Xs)}\|(XS)^{-1/2}(e-Xs)\|-\alpha^2/(2(1-\alpha))$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$ with $n>m$, let $c\in\mathbb R^n$, and suppose $\Omega=\{y: c-A^Ty\ge0\}$ is bounded with nonempty interior. Let $x$ be an interior point of $\mathcal X_\Omega$ ($Ax=0$, $x>0$) and $(y,s)$ an interior point of $\Omega$ ($s=c-A^Ty>0$), normalized so that $s^Tx=n$. Let $(d_x,d_y,d_s)$ solve the primal-dual Newton system
--   $$Sd_x+Xd_s=e-Xs,\qquad Ad_x=0,\qquad -A^Td_y-d_s=0,$$
--   let $0<\alpha<1$ be a constant and
--   $$\theta=\frac{\alpha\sqrt{\min(Xs)}}{\|(XS)^{-1/2}(e-Xs)\|},\qquad \min(v)=\min_j v_j .$$
--   Then, with the primal-dual potential $\psi_n(x,s)=n\log(x^Ts)-\sum_j\log(x_js_j)$,
--   $$\psi_n(x+\theta d_x,\,s+\theta d_s)-\psi_n(x,s)\;\le\;-\alpha\sqrt{\min(Xs)}\,\|(XS)^{-1/2}(e-Xs)\|+\frac{\alpha^2}{2(1-\alpha)} .$$
--
--   This is the per-step estimate of the primal-dual potential algorithm of §3.4.2; Theorem 3.13 turns it into a constant decrease.
--
--   **Formalization Note** The normalization $s^Tx=n$ is not in the lemma's sentence: it is the standing assumption of §3.4.2 ("Given any $x\in\mathring{\mathcal X}_\Omega$ and $s\in\mathring{\mathcal S}_\Omega$ with $s^Tx=n$", p. 103) and is an explicit hypothesis here (finding F1 shows it cannot be dropped). The chapter's standing assumptions (rank $A=m$, $n>m$, $\Omega$ bounded with nonempty interior; pp. 48, 81) are explicit too. When $Xs=e$ the book's $\theta$ is undefined; Lean's division by zero makes $\theta=0$ there.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 104, Lemma 3.12 (system (3.15), step size (3.17); normalization s^T x = n from p. 103)

import Mathlib
import Definitions.Def_YeIPA_Center_AnalyticCenter

open Matrix

namespace YeIPA.Center

/-- Lemma 3.12 (Ye 1997, p. 104). Under the standing assumptions (pp. 48, 81), let `x` be an
interior point of `X_Ω` and `(y, s)` an interior point of Ω with `sᵀx = n` (the standing
normalization of §3.4.2, p. 103). Let `(d_x, d_y, d_s)` solve the primal-dual Newton system
(3.15), let `0 < α < 1` and `θ = α √min(Xs) / ‖(XS)^{-1/2}(e − Xs)‖` (3.17). Then
`ψ_n(x + θd_x, s + θd_s) − ψ_n(x, s) ≤ −α √min(Xs) ‖(XS)^{-1/2}(e − Xs)‖ + α²/(2(1 − α))`. -/
theorem pd_potential_decrease {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (hA : StandingAssumptions A c) (x : Fin n → ℝ) (hx : IsPrimalInterior A x)
    (y : Fin m → ℝ) (s : Fin n → ℝ) (hs : IsDualInterior A c y s)
    (hsx : s ⬝ᵥ x = n)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsPDNewtonDir A x s dx dy ds)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    pdPotential (x + pdStepSize α x s • dx) (s + pdStepSize α x s • ds) - pdPotential x s ≤
      -α * Real.sqrt (vmin (fun j => x j * s j)) * scaledResidual x s
        + α ^ 2 / (2 * (1 - α)) := by sorry

end YeIPA.Center
