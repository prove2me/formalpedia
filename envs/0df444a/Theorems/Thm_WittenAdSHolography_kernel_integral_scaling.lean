-- Prove2me | Theorems.Thm_WittenAdSHolography_kernel_integral_scaling
-- name    : WittenAdSHolography.kernel_integral_scaling
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:31:42.129355+00:00
-- url     : https://prove2.me/theorems/9442a986-9009-4fd4-abbb-b68287e887d2
-- title:
--   Eq. (2.40): $\int x_0^{2\Delta-d}(x_0^2+|x|^2)^{-\Delta}\,dx$ is independent of $x_0$
-- statement:
--   Let $d\ge0$ and $\Delta>d/2$. Then $x\mapsto(1+|x|^2)^{-\Delta}$ is Lebesgue integrable on $\mathbb R^d$, and for every $x_0>0$
--   $$\int_{\mathbb R^d}\frac{x_0^{2\Delta-d}}{(x_0^2+|x|^2)^{\Delta}}\,dx=\int_{\mathbb R^d}\frac{dx}{(1+|x|^2)^{\Delta}} ,$$
--   so the left side does not depend on $x_0$.
--
--   This is the "scaling argument" Witten uses to identify the boundary limit of the kernel with a multiple of the delta function.
-- source:
--   E. Witten, Anti de Sitter Space and Holography, Adv. Theor. Math. Phys. 2 (1998) 253-291, arXiv:hep-th/9802150v2, https://arxiv.org/abs/hep-th/9802150, pp. 12, 21, eq. (2.40)

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

open WittenAdSHolography MeasureTheory Filter Topology

theorem WittenAdSHolography.kernel_integral_scaling (d : ℕ) (Δ : ℝ) (hΔ : (d : ℝ) / 2 < Δ) :
    Integrable (fun x : Bdry d => (1 + ‖x‖ ^ 2) ^ (-Δ)) ∧
      ∀ x₀ : ℝ, 0 < x₀ →
        ∫ x : Bdry d, x₀ ^ (2 * Δ - d) / (x₀ ^ 2 + ‖x‖ ^ 2) ^ Δ =
          ∫ x : Bdry d, (1 + ‖x‖ ^ 2) ^ (-Δ) := by sorry
