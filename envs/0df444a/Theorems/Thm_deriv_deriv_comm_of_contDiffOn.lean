-- Prove2me | Theorems.Thm_deriv_deriv_comm_of_contDiffOn
-- name    : deriv_deriv_comm_of_contDiffOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/4588b7fc-4ad8-5e15-a485-aa39cd634649
-- title:
--   Schwarz symmetry for nested derivatives at the origin
-- statement:
--   Let $F : \mathbb{R} \to \mathbb{R} \to \mathbb{C}$ be a function of two real variables with complex values, let $U$ be a subset of $\mathbb{R} \times \mathbb{R}$, assume $U$ is open and that the origin $(0,0)$ lies in $U$, and assume that the uncurried function $p \mapsto F(p_1, p_2)$ is twice continuously differentiable on $U$ in the sense of `ContDiffOn ℝ 2`. Then the two nested one-variable derivatives at the origin agree: the derivative at $0$ of the function $s \mapsto \bigl(\text{derivative at } 0 \text{ of } t \mapsto F(s,t)\bigr)$ equals the derivative at $0$ of the function $t \mapsto \bigl(\text{derivative at } 0 \text{ of } s \mapsto F(s,t)\bigr)$. Here the derivatives are Mathlib's total `deriv` on functions $\mathbb{R} \to \mathbb{C}$, so in each nested expression the inner derivative is formed at the point $0$ for every value of the outer variable, including those for which the relevant slice need not meet $U$, and no differentiability is asserted of the intermediate functions beyond what the conclusion requires.
--
--   This is the Schwarz–Clairaut symmetry of second partial derivatives, in the shape needed when $F$ is only assumed $C^2$ on an open neighbourhood of the origin rather than on all of $\mathbb{R}^2$, and with the partial derivatives written as iterated one-variable `deriv`s. It is used in the computation of the action of the Casimir element on archimedean lifts in [`LanglandsTunnell.CubicInduction.casimir_apply_eq_sum_deriv_archRealLift3_mul`](thm.html#LanglandsTunnell.CubicInduction.casimir_apply_eq_sum_deriv_archRealLift3_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_deriv_deriv_comm_of_contDiffOn.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem deriv_deriv_comm_of_contDiffOn
    (F : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)) (hU : IsOpen U) (h0 : ((0 : ℝ), (0 : ℝ)) ∈ U)
    (hF : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) U) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => F s t) 0) 0
      = deriv (fun t : ℝ => deriv (fun s : ℝ => F s t) 0) 0 := by sorry
