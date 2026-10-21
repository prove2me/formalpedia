-- Prove2me | Theorems.Thm_WrightPDIPM_SelfDual_theorem_9_2
-- name    : WrightPDIPM.SelfDual.theorem_9_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:12.08991+00:00
-- url     : https://prove2.me/theorems/41bda0be-0327-407d-8e47-7ceba9def084
-- title:
--   Theorem 9.2 — Ω ≠ ∅ iff every strictly complementary solution of the simplified HSD mLCP (9.5) has τ* > 0 and κ* = 0
-- statement:
--   Let $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$ (no rank assumption) and let $\Omega$ be the primal-dual solution set of the pair (9.3a) $\min c^{\mathsf T}x$ s.t. $Ax = b$, $x \ge 0$ and (9.3b) $\max b^{\mathsf T}\lambda$ s.t. $A^{\mathsf T}\lambda + s = c$, $s \ge 0$. A solution of the simplified HSD mLCP (9.5) is a tuple $(\tau, x, \lambda, \kappa, s)$ with $\tau, \kappa \in \mathbb R$, $x, s \in \mathbb R^n$, $\lambda \in \mathbb R^m$ and
--   $$\kappa = -c^{\mathsf T}x + b^{\mathsf T}\lambda,\quad s = c\tau - A^{\mathsf T}\lambda,\quad 0 = -b\tau + Ax,\quad (\tau, x, \kappa, s) \ge 0,\quad \tau\kappa + x^{\mathsf T}s = 0;$$
--   it is strictly complementary if $\tau + \kappa > 0$ and $x + s > 0$. Then
--   $$\Omega \ne \emptyset \iff \text{every strictly complementary solution } (\tau^*, x^*, \lambda^*, \kappa^*, s^*) \text{ of (9.5) has } \tau^* > 0 \text{ and } \kappa^* = 0.$$
--
--   The simplified HSD form always has strictly complementary solutions, so solving one problem that is guaranteed to be solvable decides whether the original LP pair has a solution; when it does, $(x^*, \lambda^*, s^*)/\tau^*$ is one.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 181, Theorem 9.2

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup

namespace WrightPDIPM.SelfDual

open Matrix

/-- Theorem 9.2 (p. 181): the primal-dual solution set `Ω` for (9.3) is nonempty if and only if
all strictly complementary solutions `(τ*, x*, λ*, κ*, s*)` of (9.5) have `τ* > 0` and
`κ* = 0`. -/
theorem theorem_9_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    (Omega A b c).Nonempty ↔
      ∀ (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (κ : ℝ) (s : Fin n → ℝ),
        IsStrictlyComplementary95 A b c τ x lam κ s → 0 < τ ∧ κ = 0 := by sorry

end WrightPDIPM.SelfDual
