-- Prove2me | Theorems.Thm_WrightPDIPM_SelfDual_theorem_9_5
-- name    : WrightPDIPM.SelfDual.theorem_9_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:11.68439+00:00
-- url     : https://prove2.me/theorems/2603fb11-eb8e-46e7-a8d1-1b4800046bf9
-- title:
--   Theorem 9.5 — Ω ≠ ∅ iff every strictly complementary solution of the HSD mLCP (9.8) has τ* > 0 and κ* = 0
-- statement:
--   Let $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, let $\Omega$ be the primal-dual solution set of the pair (9.3), and let $(x^0, \lambda^0, s^0)$ be an initial point with $x^0 > 0$, $s^0 > 0$, defining $\bar b = b - Ax^0$, $\bar c = c - A^{\mathsf T}\lambda^0 - s^0$, $\bar z = c^{\mathsf T}x^0 + 1 - b^{\mathsf T}\lambda^0$ and the HSD mLCP (9.8):
--   $$\kappa = -c^{\mathsf T}x + b^{\mathsf T}\lambda + \bar z\theta,\quad s = c\tau - A^{\mathsf T}\lambda - \bar c\theta,\quad 0 = -b\tau + Ax + \bar b\theta,\quad 0 = -\bar z\tau + \bar c^{\mathsf T}x - \bar b^{\mathsf T}\lambda + (x^0)^{\mathsf T}s^0 + 1,$$
--   $(\tau, x, \kappa, s) \ge 0$, $\tau\kappa + x^{\mathsf T}s = 0$. A solution is strictly complementary if $\tau + \kappa > 0$ and $x + s > 0$. Then
--   $$\Omega \ne \emptyset \iff \text{every strictly complementary solution } (\tau^*, x^*, \lambda^*, \theta^*, \kappa^*, s^*) \text{ of (9.8) has } \tau^* > 0 \text{ and } \kappa^* = 0.$$
--
--   This transfers Theorem 9.2 to the HSD form of Ye, Todd and Mizuno, which has a strictly feasible starting point.
--
--   **Formalization Note** The standing assumption $x^0 > 0$, $s^0 > 0$ of the HSD form (p. 183) is stated explicitly. The book leaves the proof as an exercise.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 185, Theorem 9.5

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup

namespace WrightPDIPM.SelfDual

open Matrix

/-- Theorem 9.5 (p. 185): for an initial point `(x⁰, λ⁰, s⁰)` with `x⁰ > 0`, `s⁰ > 0` (p. 183),
the primal-dual solution set `Ω` for (9.3) is nonempty if and only if all strictly
complementary solutions `(τ*, x*, λ*, θ*, κ*, s*)` of (9.8) have `τ* > 0` and `κ* = 0`. -/
theorem theorem_9_5 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j) :
    (Omega A b c).Nonempty ↔
      ∀ (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ),
        IsStrictlyComplementary98 A b c x0 lam0 s0 τ x lam θ κ s → 0 < τ ∧ κ = 0 := by sorry

end WrightPDIPM.SelfDual
