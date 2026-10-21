-- Prove2me | Theorems.Thm_YeIPA_Center_proximity_measures_equivalent
-- name    : YeIPA.Center.proximity_measures_equivalent
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:00.922976+00:00
-- url     : https://prove2.me/theorems/0a42e062-a398-441a-98fb-191201547760
-- title:
--   Theorem 3.2 — the proximity measures $\eta_d$, $\eta_p$, $\eta$ are equivalent and $\eta<1$ bounds the potential gaps and the distance to the analytic center
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have rank $m$ with $n>m$, let $c\in\mathbb R^n$, and suppose $\Omega=\{y: c-A^Ty\ge0\}$ is bounded with nonempty interior. Let $(y,s)$ be an interior point of $\Omega$ ($s=c-A^Ty>0$), $(y^a,s^a)$ the analytic center of $\Omega$ (the interior point maximizing $\mathcal B(y)=\sum_j\log s_j$), $x$ an interior point of $\mathcal X_\Omega=\{x: Ax=0,\ x\ge0\}$, and $x^a$ the primal potential minimizer with $c^Tx^a=n$ (the interior point of $\mathcal X_\Omega$ with $c^Tx^a=n$ minimizing $\mathcal P(x)=n\log(c^Tx)-\sum_j\log x_j$). With the Euclidean norm, the proximity measures
--   $$\eta_d(s)=\|S^{-1}A^T(AS^{-2}A^T)^{-1}AS^{-1}e\|,\qquad \eta_p(x)=\|(I-XA^T(AX^2A^T)^{-1}AX)(Xc-e)\|,\qquad \eta(x,s)=\|Xs-e\|,$$
--   and the primal-dual potential $\psi_n(x,s)=n\log(x^Ts)-\sum_j\log(x_js_j)$, the following hold.
--
--   1. $\eta_d(s)\le\eta(x,s)$ and $\eta_p(x)\le\eta(x,s)$. Conversely, if $\eta_d(s)<1$ there is an interior point $x'$ of $\mathcal X_\Omega$ with $\eta(x',s)\le\eta_d(s)$, and if $\eta_p(x)<1$ there is an interior point $(y',s')$ of $\Omega$ with $\eta(x,s')\le\eta_p(x)$.
--   2. If $\eta(x,s)<1$, there is $\hat x\ge0$ with $A\hat x=0$ and $c^T\hat x=s^T\hat x=n$ such that
--   $$\eta(\hat x,s)\le\frac{\eta(x,s)}{\sqrt{1-\eta(x,s)^2/n}} .$$
--   3. If $\eta(x,s)<1$ and $c^Tx=n$, then each of
--   $$\psi_n(x,s)-\psi_n(x^a,s^a),\qquad \mathcal P(x)-\mathcal P(x^a),\qquad \mathcal B(y^a)-\mathcal B(y)$$
--   is at most $\dfrac{\eta(x,s)^2}{2(1-\eta(x,s))}$.
--   4. If $\eta(x,s)<1$, then
--   $$\|S^{-1}s^a-e\|\le\frac{\eta(x,s)}{1-\eta(x,s)}\qquad\text{and}\qquad\|X^{-1}x^a-e\|\le\frac{\eta(x,s)}{1-\eta(x,s)} .$$
--
--   The theorem says the dual, primal and primal-dual measures of proximity to the analytic center are interchangeable: if one is small, all are, and a point with $\eta<1$ is an approximate analytic center in the sense of potential value and of relative distance. Chapter 3's algorithms use whichever measure suits them.
--
--   **Formalization Note** The standing assumptions of the chapter (rank $A=m$, $n>m$, $\Omega$ bounded with nonempty interior; pp. 48, 81) are explicit hypotheses. The book names the partner points in (i) $x(s)$ and $s(x)$ (formulas (3.3), (3.6)); the statement asserts their existence, as the book's sentence does. Only part 3 assumes $c^Tx=n$, as on the page. $\mathcal B$ is evaluated on slack vectors, $\mathcal B(y)=\sum_j\log s_j$ with $s=c-A^Ty$. In 2, $\eta(x,s)^2/n$ is real division with $n\ge 1$. $\|S^{-1}s^a-e\|$ is the Euclidean norm of the vector $(s^a_j/s_j-1)_j$, likewise for $x$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, pp. 84–85, Theorem 3.2

import Mathlib
import Definitions.Def_YeIPA_Center_AnalyticCenter

open Matrix

namespace YeIPA.Center

/-- Theorem 3.2 (Ye 1997, pp. 84–85). Under the standing assumptions (rank `A = m`, `n > m`,
Ω bounded with nonempty interior; pp. 48, 81), let `(y, s)` be an interior point of Ω,
`(yᵃ, sᵃ)` the analytic center of Ω, `x` an interior point of `X_Ω` and `xᵃ` the primal
potential minimizer with `cᵀxᵃ = n`. Then, writing `η = η(x, s)`:
(i) `η_d(s) ≤ η` and `η_p(x) ≤ η`; if `η_d(s) < 1` there is an interior `x'` of `X_Ω` with
`η(x', s) ≤ η_d(s)`; if `η_p(x) < 1` there is an interior `(y', s')` of Ω with
`η(x, s') ≤ η_p(x)`.
(ii) if `η < 1`, there is `x̂ ≥ 0` with `Ax̂ = 0`, `cᵀx̂ = sᵀx̂ = n` and
`η(x̂, s) ≤ η / √(1 − η²/n)`.
(iii) if `η < 1` and `cᵀx = n`, then `ψ_n(x, s) − ψ_n(xᵃ, sᵃ)`, `P(x) − P(xᵃ)` and
`B(yᵃ) − B(y)` are each at most `η² / (2(1 − η))`.
(iv) if `η < 1`, then `‖S⁻¹sᵃ − e‖ ≤ η/(1 − η)` and `‖X⁻¹xᵃ − e‖ ≤ η/(1 − η)`. -/
theorem proximity_measures_equivalent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (hA : StandingAssumptions A c)
    (y : Fin m → ℝ) (s : Fin n → ℝ) (hs : IsDualInterior A c y s)
    (ya : Fin m → ℝ) (sa : Fin n → ℝ) (hsa : IsAnalyticCenter A c ya sa)
    (x : Fin n → ℝ) (hx : IsPrimalInterior A x)
    (xa : Fin n → ℝ) (hxa : IsPrimalPotentialMinimizer A c xa) :
    -- (i)
    (etaD A s ≤ eta x s ∧ etaP A c x ≤ eta x s ∧
      (etaD A s < 1 → ∃ x' : Fin n → ℝ, IsPrimalInterior A x' ∧ eta x' s ≤ etaD A s) ∧
      (etaP A c x < 1 → ∃ (y' : Fin m → ℝ) (s' : Fin n → ℝ),
        IsDualInterior A c y' s' ∧ eta x s' ≤ etaP A c x)) ∧
    -- (ii)
    (eta x s < 1 → ∃ xh : Fin n → ℝ, (∀ j, 0 ≤ xh j) ∧ A *ᵥ xh = 0 ∧ c ⬝ᵥ xh = n ∧
      s ⬝ᵥ xh = n ∧ eta xh s ≤ eta x s / Real.sqrt (1 - eta x s ^ 2 / n)) ∧
    -- (iii)
    (eta x s < 1 → c ⬝ᵥ x = n →
      pdPotential x s - pdPotential xa sa ≤ eta x s ^ 2 / (2 * (1 - eta x s)) ∧
      primalPotential c x - primalPotential c xa ≤ eta x s ^ 2 / (2 * (1 - eta x s)) ∧
      dualPotential sa - dualPotential s ≤ eta x s ^ 2 / (2 * (1 - eta x s))) ∧
    -- (iv)
    (eta x s < 1 →
      norm2 (fun j => sa j / s j - 1) ≤ eta x s / (1 - eta x s) ∧
      norm2 (fun j => xa j / x j - 1) ≤ eta x s / (1 - eta x s)) := by sorry

end YeIPA.Center
