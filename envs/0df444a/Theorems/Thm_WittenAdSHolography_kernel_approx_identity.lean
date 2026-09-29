-- Prove2me | Theorems.Thm_WittenAdSHolography_kernel_approx_identity
-- name    : WittenAdSHolography.kernel_approx_identity
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:32:45.930028+00:00
-- url     : https://prove2.me/theorems/c0324c3d-677f-412a-83e3-5ae8ffda016e
-- title:
--   Eq. (2.39): $x_0^{2\Delta-d}(x_0^2+|x|^2)^{-\Delta}\to C_\Delta\,\delta(x)$ as $x_0\to0^+$
-- statement:
--   Let $d\ge0$, $\Delta>d/2$, and $C_\Delta=\int_{\mathbb R^d}(1+|u|^2)^{-\Delta}\,du$. For every bounded continuous $\varphi_0:\mathbb R^d\to\mathbb R$ and every $x\in\mathbb R^d$,
--   $$\lim_{x_0\to0^+}\int_{\mathbb R^d}\frac{x_0^{2\Delta-d}}{(x_0^2+|x-x'|^2)^{\Delta}}\,\varphi_0(x')\,dx'=C_\Delta\,\varphi_0(x).$$
--
--   In distributional language: the kernels converge to $C_\Delta\,\delta$, which is how Witten reads off the boundary behaviour of the Poisson-type integral (2.41).
-- source:
--   E. Witten, Anti de Sitter Space and Holography, Adv. Theor. Math. Phys. 2 (1998) 253-291, arXiv:hep-th/9802150v2, https://arxiv.org/abs/hep-th/9802150, p. 21, eq. (2.39)

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

open WittenAdSHolography MeasureTheory Filter Topology

theorem WittenAdSHolography.kernel_approx_identity (d : ℕ) (Δ : ℝ) (hΔ : (d : ℝ) / 2 < Δ) (φ₀ : Bdry d → ℝ)
    (hcont : Continuous φ₀) (hbdd : ∃ B : ℝ, ∀ x, |φ₀ x| ≤ B) (x : Bdry d) :
    Tendsto
      (fun x₀ : ℝ => ∫ x' : Bdry d, x₀ ^ (2 * Δ - d) / (x₀ ^ 2 + ‖x - x'‖ ^ 2) ^ Δ * φ₀ x')
      (𝓝[>] 0) (𝓝 ((∫ u : Bdry d, (1 + ‖u‖ ^ 2) ^ (-Δ)) * φ₀ x)) := by sorry
