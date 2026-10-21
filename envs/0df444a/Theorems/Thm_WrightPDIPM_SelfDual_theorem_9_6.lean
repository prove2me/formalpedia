-- Prove2me | Theorems.Thm_WrightPDIPM_SelfDual_theorem_9_6
-- name    : WrightPDIPM.SelfDual.theorem_9_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:14.348982+00:00
-- url     : https://prove2.me/theorems/1b63c02c-d0e6-4c8c-aa26-b73ee06db7a0
-- title:
--   Theorem 9.6 — a strictly complementary solution of (9.8) with κ* > 0 certifies primal or dual infeasibility
-- statement:
--   Let $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, and let $(x^0, \lambda^0, s^0)$ be an initial point with $x^0 > 0$, $s^0 > 0$, defining $\bar b = b - Ax^0$, $\bar c = c - A^{\mathsf T}\lambda^0 - s^0$, $\bar z = c^{\mathsf T}x^0 + 1 - b^{\mathsf T}\lambda^0$. Let $(\tau^*, x^*, \lambda^*, \theta^*, \kappa^*, s^*)$ be a strictly complementary solution of the HSD mLCP (9.8),
--   $$\kappa^* = -c^{\mathsf T}x^* + b^{\mathsf T}\lambda^* + \bar z\theta^*,\quad s^* = c\tau^* - A^{\mathsf T}\lambda^* - \bar c\theta^*,\quad 0 = -b\tau^* + Ax^* + \bar b\theta^*,\quad 0 = -\bar z\tau^* + \bar c^{\mathsf T}x^* - \bar b^{\mathsf T}\lambda^* + (x^0)^{\mathsf T}s^0 + 1,$$
--   $(\tau^*, x^*, \kappa^*, s^*) \ge 0$, $\tau^*\kappa^* + (x^*)^{\mathsf T}s^* = 0$, $\tau^* + \kappa^* > 0$, $x^* + s^* > 0$, and suppose $\kappa^* > 0$. Then at least one of $c^{\mathsf T}x^*$ and $-b^{\mathsf T}\lambda^*$ is negative, and
--
--   1. if $c^{\mathsf T}x^* < 0$, the dual problem (9.3b) is infeasible;
--   2. if $-b^{\mathsf T}\lambda^* < 0$, the primal problem (9.3a) is infeasible.
--
--   This transfers Theorem 9.3 to the HSD form.
--
--   **Formalization Note** The page writes the solution tuple as $(\tau^*, x^*, \lambda^*, \theta^*, \kappa^*, z^*)$; $z^*$ is a misprint for $s^*$, the last block of (9.8). The standing assumption $x^0 > 0$, $s^0 > 0$ (p. 183) is stated explicitly. The book leaves the proof as an exercise.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 185, Theorem 9.6

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup

namespace WrightPDIPM.SelfDual

open Matrix

/-- Theorem 9.6 (p. 185): for an initial point `(x⁰, λ⁰, s⁰)` with `x⁰ > 0`, `s⁰ > 0` (p. 183),
if `(τ*, x*, λ*, θ*, κ*, s*)` is a strictly complementary solution of (9.8) with `κ* > 0` (the
page prints `z*` for `s*`, a misprint), then at least one of `cᵀx*` and `−bᵀλ*` is negative,
and if `cᵀx* < 0` the dual problem (9.3b) is infeasible, and if `−bᵀλ* < 0` the primal
problem (9.3a) is infeasible. -/
theorem theorem_9_6 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ)
    (hsc : IsStrictlyComplementary98 A b c x0 lam0 s0 τ x lam θ κ s) (hκ : 0 < κ) :
    (c ⬝ᵥ x < 0 ∨ -(b ⬝ᵥ lam) < 0) ∧
    (c ⬝ᵥ x < 0 → ¬ ∃ (lam' : Fin m → ℝ) (s' : Fin n → ℝ), DualFeasible A c lam' s') ∧
    (-(b ⬝ᵥ lam) < 0 → ¬ ∃ x' : Fin n → ℝ, PrimalFeasible A b x') := by sorry

end WrightPDIPM.SelfDual
