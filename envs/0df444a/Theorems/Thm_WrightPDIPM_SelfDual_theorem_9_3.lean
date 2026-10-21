-- Prove2me | Theorems.Thm_WrightPDIPM_SelfDual_theorem_9_3
-- name    : WrightPDIPM.SelfDual.theorem_9_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:10.160618+00:00
-- url     : https://prove2.me/theorems/f56a75e7-d96a-4c48-ac90-1077bb693fb5
-- title:
--   Theorem 9.3 — a strictly complementary solution of (9.5) with κ* > 0 certifies primal or dual infeasibility
-- statement:
--   Let $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, and let $(\tau^*, x^*, \lambda^*, \kappa^*, s^*)$ be a strictly complementary solution of the simplified HSD mLCP (9.5), i.e.
--   $$\kappa^* = -c^{\mathsf T}x^* + b^{\mathsf T}\lambda^*,\quad s^* = c\tau^* - A^{\mathsf T}\lambda^*,\quad 0 = -b\tau^* + Ax^*,\quad (\tau^*, x^*, \kappa^*, s^*) \ge 0,\quad \tau^*\kappa^* + (x^*)^{\mathsf T}s^* = 0,$$
--   with $\tau^* + \kappa^* > 0$ and $x^* + s^* > 0$, and suppose $\kappa^* > 0$. Then at least one of $c^{\mathsf T}x^*$ and $-b^{\mathsf T}\lambda^*$ is negative, and
--
--   1. if $c^{\mathsf T}x^* < 0$, the dual problem (9.3b) ($A^{\mathsf T}\lambda + s = c$, $s \ge 0$) is infeasible;
--   2. if $-b^{\mathsf T}\lambda^* < 0$, the primal problem (9.3a) ($Ax = b$, $x \ge 0$) is infeasible.
--
--   Together with Theorem 9.2 this makes a strictly complementary solution of (9.5) a certificate either of a solution of the LP pair or of infeasibility.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 182, Theorem 9.3

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup

namespace WrightPDIPM.SelfDual

open Matrix

/-- Theorem 9.3 (p. 182): if `(τ*, x*, λ*, κ*, s*)` is a strictly complementary solution of
(9.5) with `κ* > 0`, then at least one of `cᵀx*` and `−bᵀλ*` is negative, and if `cᵀx* < 0`
the dual problem (9.3b) is infeasible, and if `−bᵀλ* < 0` the primal problem (9.3a) is
infeasible. -/
theorem theorem_9_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (κ : ℝ) (s : Fin n → ℝ)
    (hsc : IsStrictlyComplementary95 A b c τ x lam κ s) (hκ : 0 < κ) :
    (c ⬝ᵥ x < 0 ∨ -(b ⬝ᵥ lam) < 0) ∧
    (c ⬝ᵥ x < 0 → ¬ ∃ (lam' : Fin m → ℝ) (s' : Fin n → ℝ), DualFeasible A c lam' s') ∧
    (-(b ⬝ᵥ lam) < 0 → ¬ ∃ x' : Fin n → ℝ, PrimalFeasible A b x') := by sorry

end WrightPDIPM.SelfDual
