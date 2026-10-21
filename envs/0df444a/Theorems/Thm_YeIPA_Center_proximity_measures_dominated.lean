-- Prove2me | Theorems.Thm_YeIPA_Center_proximity_measures_dominated
-- name    : YeIPA.Center.proximity_measures_dominated
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:05.23121+00:00
-- url     : https://prove2.me/theorems/c3a76da2-90bd-4a76-8eaa-6798c0c47006
-- title:
--   Theorem 3.2 (i) — $\eta_d(s)\le\eta(x,s)$ and $\eta_p(x)\le\eta(x,s)$, and conversely
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$ with $n>m$, let $c\in\mathbb R^n$, and suppose $\Omega=\{y: c-A^Ty\ge0\}$ is bounded with nonempty interior. Let $(y,s)$ be an interior point of $\Omega$ ($s=c-A^Ty>0$) and $x$ an interior point of $\mathcal X_\Omega$ ($Ax=0$, $x>0$). With the proximity measures
--   $$\eta_d(s)=\|S^{-1}A^T(AS^{-2}A^T)^{-1}AS^{-1}e\|,\qquad \eta_p(x)=\|(I-XA^T(AX^2A^T)^{-1}AX)(Xc-e)\|,\qquad \eta(x,s)=\|Xs-e\|$$
--   (Euclidean norm), the following hold.
--
--   1. $\eta_d(s)\le\eta(x,s)$ and $\eta_p(x)\le\eta(x,s)$.
--   2. If $\eta_d(s)<1$, there is an interior point $x'$ of $\mathcal X_\Omega$ with $\eta(x',s)\le\eta_d(s)$.
--   3. If $\eta_p(x)<1$, there is an interior point $(y',s')$ of $\Omega$ with $\eta(x,s')\le\eta_p(x)$.
--
--   So the dual measure and the primal measure are both dominated by the primal-dual one, and each of them, when below $1$, is attained by the primal-dual measure at a suitable partner point. This is part (i) of Theorem 3.2, the mission's goal.
--
--   **Formalization Note** The book names the partner points $x(s)$ of (3.3) and $s(x)$ of (3.6); the statement asserts existence, as the book's sentence does. The standing assumptions of the chapter (rank $A=m$, $n>m$, $\Omega$ bounded with nonempty interior; pp. 48, 81) are explicit hypotheses. Vectors are `Fin n → ℝ`.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 84, Theorem 3.2 (i)

import Mathlib
import Definitions.Def_YeIPA_Center_AnalyticCenter

open Matrix

namespace YeIPA.Center

/-- Theorem 3.2 (i) (Ye 1997, p. 84). Under the standing assumptions (rank `A = m`, `n > m`,
Ω bounded with nonempty interior; pp. 48, 81), let `(y, s)` be an interior point of Ω and `x`
an interior point of `X_Ω`. Then `η_d(s) ≤ η(x, s)` and `η_p(x) ≤ η(x, s)`. Conversely, if
`η_d(s) < 1` there is an interior point `x'` of `X_Ω` with `η(x', s) ≤ η_d(s)`, and if
`η_p(x) < 1` there is an interior point `(y', s')` of Ω with `η(x, s') ≤ η_p(x)`. -/
theorem proximity_measures_dominated {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (hA : StandingAssumptions A c)
    (y : Fin m → ℝ) (s : Fin n → ℝ) (hs : IsDualInterior A c y s)
    (x : Fin n → ℝ) (hx : IsPrimalInterior A x) :
    etaD A s ≤ eta x s ∧ etaP A c x ≤ eta x s ∧
      (etaD A s < 1 → ∃ x' : Fin n → ℝ, IsPrimalInterior A x' ∧ eta x' s ≤ etaD A s) ∧
      (etaP A c x < 1 → ∃ (y' : Fin m → ℝ) (s' : Fin n → ℝ),
        IsDualInterior A c y' s' ∧ eta x s' ≤ etaP A c x) := by sorry

end YeIPA.Center
