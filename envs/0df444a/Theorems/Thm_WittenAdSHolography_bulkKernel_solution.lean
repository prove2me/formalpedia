-- Prove2me | Theorems.Thm_WittenAdSHolography_bulkKernel_solution
-- name    : WittenAdSHolography.bulkKernel_solution
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:27:49.664304+00:00
-- url     : https://prove2.me/theorems/5c96f61e-2adc-4f63-b5ca-b9635712a6d6
-- title:
--   Eqs. (2.18)–(2.19), (2.38): $x_0^{\Delta}/(x_0^2+|x|^2)^{\Delta}$ solves $\Delta_g u=m^2u$
-- statement:
--   Let $d\ge0$ and $m^2,\Delta\in\mathbb R$ with $\Delta(\Delta-d)=m^2$. Then the bulk-to-boundary kernel
--   $$K_\Delta(x_0,x)=\frac{x_0^{\Delta}}{(x_0^2+|x|^2)^{\Delta}}$$
--   is a $C^2$ solution of $\Delta_gK_\Delta=m^2K_\Delta$ on the upper half space $\{x_0>0\}$.
--
--   It is obtained from $x_0^{\Delta}$ by the inversion $x_i\mapsto x_i/(x_0^2+|x|^2)$, an isometry of hyperbolic space, and is the Green's function with pole at the boundary point $x=0$ used to build the Poisson-type integral (2.41).
-- source:
--   E. Witten, Anti de Sitter Space and Holography, Adv. Theor. Math. Phys. 2 (1998) 253-291, arXiv:hep-th/9802150v2, https://arxiv.org/abs/hep-th/9802150, pp. 12, 21, eqs. (2.18)-(2.19), (2.38)

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

open WittenAdSHolography MeasureTheory Filter Topology

theorem WittenAdSHolography.bulkKernel_solution (d : ℕ) (msq Δ : ℝ) (hΔ : Δ * (Δ - d) = msq) :
    IsMassiveSolution d msq (fun x₀ x => bulkKernel Δ x₀ x) := by sorry
