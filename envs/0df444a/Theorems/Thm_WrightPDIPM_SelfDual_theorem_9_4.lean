-- Prove2me | Theorems.Thm_WrightPDIPM_SelfDual_theorem_9_4
-- name    : WrightPDIPM.SelfDual.theorem_9_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:14.521544+00:00
-- url     : https://prove2.me/theorems/69f97227-b510-4510-912b-3b0a65f473fd
-- title:
--   Theorem 9.4 — every solution of the HSD mLCP (9.8) has θ* = 0
-- statement:
--   Let $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, and let $(x^0, \lambda^0, s^0)$ be an initial point with $x^0 > 0$ and $s^0 > 0$. Put $\bar b = b - Ax^0$, $\bar c = c - A^{\mathsf T}\lambda^0 - s^0$, $\bar z = c^{\mathsf T}x^0 + 1 - b^{\mathsf T}\lambda^0$. If $(\tau^*, x^*, \lambda^*, \theta^*, \kappa^*, s^*)$ is any solution of the HSD mLCP (9.8), that is,
--   $$\begin{aligned}\kappa^* &= -c^{\mathsf T}x^* + b^{\mathsf T}\lambda^* + \bar z\theta^*, & s^* &= c\tau^* - A^{\mathsf T}\lambda^* - \bar c\theta^*,\\ 0 &= -b\tau^* + Ax^* + \bar b\theta^*, & 0 &= -\bar z\tau^* + \bar c^{\mathsf T}x^* - \bar b^{\mathsf T}\lambda^* + (x^0)^{\mathsf T}s^0 + 1,\end{aligned}$$
--   $(\tau^*, x^*, \kappa^*, s^*) \ge 0$ and $\tau^*\kappa^* + (x^*)^{\mathsf T}s^* = 0$, then
--   $$\theta^* = 0.$$
--
--   The variable $\theta$ scales the infeasibility of the initial point; its vanishing at every solution is what makes the HSD form behave like the simplified form near the solution set.
--
--   **Formalization Note** The standing assumption $x^0 > 0$, $s^0 > 0$ of the HSD form (p. 183) is stated explicitly.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 184, Theorem 9.4

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup

namespace WrightPDIPM.SelfDual

open Matrix

/-- Theorem 9.4 (p. 184): for an initial point `(x⁰, λ⁰, s⁰)` with `x⁰ > 0`, `s⁰ > 0` (p. 183),
if `(τ*, x*, λ*, θ*, κ*, s*)` is any solution of (9.8), then `θ* = 0`. -/
theorem theorem_9_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ)
    (hsol : IsSolution98 A b c x0 lam0 s0 τ x lam θ κ s) :
    θ = 0 := by sorry

end WrightPDIPM.SelfDual
