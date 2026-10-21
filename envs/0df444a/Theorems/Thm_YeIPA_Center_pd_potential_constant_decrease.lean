-- Prove2me | Theorems.Thm_YeIPA_Center_pd_potential_constant_decrease
-- name    : YeIPA.Center.pd_potential_constant_decrease
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:02.582992+00:00
-- url     : https://prove2.me/theorems/d6015163-c535-4384-ad6e-c59c9ac5b481
-- title:
--   Theorem 3.13 — for $\eta(x,s)\ge\eta$ some constant $\alpha$ lowers $\psi_n$ by a constant $\delta>0$
-- statement:
--   For every constant $0<\eta<1$ there exist constants $0<\alpha<1$ and $\delta>0$, depending only on $\eta$, with the following property. Let $A\in\mathbb R^{m\times n}$ (any $m$, $n$) have rank $m$ with $n>m$, let $c\in\mathbb R^n$, and suppose $\Omega=\{y: c-A^Ty\ge0\}$ is bounded with nonempty interior. Let $x$ be an interior point of $\mathcal X_\Omega$ ($Ax=0$, $x>0$) and $(y,s)$ an interior point of $\Omega$ ($s=c-A^Ty>0$) with $s^Tx=n$ and
--   $$\eta(x,s)=\|Xs-e\|\ge\eta .$$
--   Let $(d_x,d_y,d_s)$ solve the primal-dual Newton system $Sd_x+Xd_s=e-Xs$, $Ad_x=0$, $-A^Td_y-d_s=0$, and let $\theta=\alpha\sqrt{\min(Xs)}/\|(XS)^{-1/2}(e-Xs)\|$. Then
--   $$\psi_n(x+\theta d_x,\,s+\theta d_s)-\psi_n(x,s)\le-\delta .$$
--
--   So away from the analytic center, one damped primal-dual Newton step lowers the potential $\psi_n$ by a constant independent of the problem size and data; this is what bounds the number of steps of the primal-dual potential algorithm.
--
--   **Formalization Note** The book says "we can choose $\alpha$ such that … for a positive constant $\delta$". The proof chooses $\alpha$ and $\delta$ from $\eta$ alone, uniformly in $n$, $A$, $c$ and $(x,s)$, so both are quantified before the instance. The normalization $s^Tx=n$ is the standing assumption of §3.4.2 (p. 103), and the chapter's standing assumptions (rank $A=m$, $n>m$, $\Omega$ bounded with nonempty interior; pp. 48, 81) are explicit hypotheses.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 105, Theorem 3.13 (with Lemma 3.12, p. 104; normalization s^T x = n from p. 103)

import Mathlib
import Definitions.Def_YeIPA_Center_AnalyticCenter

open Matrix

namespace YeIPA.Center

/-- Theorem 3.13 (Ye 1997, p. 105). For every constant `0 < η < 1` there are constants
`0 < α < 1` and `δ > 0`, depending only on `η`, such that for every instance satisfying the
standing assumptions (pp. 48, 81), every interior `x ∈ X_Ω` and `(y, s) ∈ Ω` with `sᵀx = n`
(p. 103) and `η(x, s) ≥ η`, and every solution `(d_x, d_y, d_s)` of (3.15), the step
`θ` of (3.17) gives `ψ_n(x + θd_x, s + θd_s) − ψ_n(x, s) ≤ −δ`. -/
theorem pd_potential_constant_decrease (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ), StandingAssumptions A c →
        ∀ (x : Fin n → ℝ), IsPrimalInterior A x →
        ∀ (y : Fin m → ℝ) (s : Fin n → ℝ), IsDualInterior A c y s → s ⬝ᵥ x = n →
        η ≤ eta x s →
        ∀ (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ), IsPDNewtonDir A x s dx dy ds →
          pdPotential (x + pdStepSize α x s • dx) (s + pdStepSize α x s • ds)
            - pdPotential x s ≤ -δ := by sorry

end YeIPA.Center
