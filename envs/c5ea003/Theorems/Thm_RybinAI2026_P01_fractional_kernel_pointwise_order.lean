-- Prove2me | Theorems.Thm_RybinAI2026_P01_fractional_kernel_pointwise_order
-- name    : RybinAI2026.P01.fractional_kernel_pointwise_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T02:31:06.986227+00:00
-- url     : https://prove2.me/theorems/62674345-6086-4c32-8925-49bbd8871d7b
-- title:
--   Pointwise order of the finite psi kernel
-- statement:
--   For positive u<=v and r in [0,1], the finite fractional kernel u/D_u(r) increases with u, while (1+u)/D_u(r) decreases. The cross-multiplication remainders are respectively (v-u)2r(1-r) and (v-u)(2r-1)^2.
-- source:
--   The scalar pointwise comparisons are the core algebraic step in the finite-interval fractional representation route for the P01 diagonal pair-contraction proof. They follow by cross multiplication with positive denominators; the remainders are controlled by 2r(1-r)≥0 and (2r-1)^2≥0.

import Mathlib

theorem RybinAI2026.P01.fractional_kernel_pointwise_order (u v r : ℝ)
    (hu : 0 < u) (huv : u ≤ v) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    u / (2 * r * (1 - r) + u * (r ^ 2 + (1 - r) ^ 2)) ≤
        v / (2 * r * (1 - r) + v * (r ^ 2 + (1 - r) ^ 2)) ∧
      (1 + v) / (2 * r * (1 - r) + v * (r ^ 2 + (1 - r) ^ 2)) ≤
        (1 + u) / (2 * r * (1 - r) + u * (r ^ 2 + (1 - r) ^ 2)) := by
  sorry
