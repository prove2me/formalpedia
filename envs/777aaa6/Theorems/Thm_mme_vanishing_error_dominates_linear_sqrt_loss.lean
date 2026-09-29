-- Prove2me | Theorems.Thm_mme_vanishing_error_dominates_linear_sqrt_loss
-- name    : mme_vanishing_error_dominates_linear_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:05:54.127013+00:00
-- url     : https://prove2.me/theorems/7b51357f-c8ee-4eea-b9c5-ea44b9f3c345
-- title:
--   Vanishing relative error absorbs a square-root exponential loss
-- statement:
--   Let $(e_n)$ be a real sequence converging to zero, let $c>0$ be a natural number, and let $S$ be any natural scale. There is a nonnegative constant $C$ such that, for every sufficiently large $m$,
--
--   $$
--   \exp\!\left(-C\sqrt{Sm+1}\right)\le 1-e_{cm}.
--   $$
--
--   This lemma converts the vanishing relative error in a cofinal finite tensor extraction into the square-root exponential loss convention used at the finite Table-2 endpoint. It is independent of any quantitative convergence rate for $(e_n)$.
-- source:
--   Analytic loss-absorption step in the finite restriction form of Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (25) and Section 6.3 (printed pp. 58-59); https://arxiv.org/abs/2210.10173

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter Topology

set_option autoImplicit false

theorem mme_vanishing_error_dominates_linear_sqrt_loss
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (count scale : ℕ) (hcount : 0 < count) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        Real.exp
            (-C * Real.sqrt (((scale * m + 1 : ℕ) : ℝ))) ≤
          1 - error (count * m) := by sorry
