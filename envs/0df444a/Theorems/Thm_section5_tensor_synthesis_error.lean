-- Prove2me | Theorems.Thm_section5_tensor_synthesis_error
-- name    : section5_tensor_synthesis_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:32.409051+00:00
-- url     : https://prove2.me/theorems/3fb66509-2bb7-486e-804e-3cfb02a2627d
-- title:
--   Tensor-product synthesis perturbation bound
-- statement:
--   Let $(X,\mu)$ be a sigma-finite measure space, let $I$ be finite, and let $f_i,g_i\in L^2(\mu;\mathbb C)$. Suppose $\delta\ge0$ and, for every $b\in\mathbb C^I$, $\|\sum_i b_if_i\|_2\le\|b\|_2$ and $\|\sum_i b_i(f_i-g_i)\|_2\le\delta\|b\|_2$. For every $n\in\mathbb N$ and coefficient array $c\in\mathbb C^{I^n}$,
--
--   $$\int_{X^n}\left|\sum_{a\in I^n}c_a\left(\prod_{j=1}^nf_{a_j}(x_j)-\prod_{j=1}^ng_{a_j}(x_j)\right)\right|^2d\mu^{\otimes n}\le\big((1+\delta)^n-1\big)^2\sum_a|c_a|^2.$$
--
--   This provides the multivariate synthesis error from a uniform one-dimensional synthesis estimate.
-- source:
--   Original product-space auxiliary result for the multivariate sampling analysis of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D. Formalization: Solutions/Section5ProductSampling.lean, lines 272–300.

import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_l2_add_bound
import Theorems.Thm_section5_product_synthesis_bound
import Theorems.Thm_section5_tensor_synthesis_bound
set_option autoImplicit false
open MeasureTheory

theorem section5_tensor_synthesis_error {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [SigmaFinite μ] (f g : ι → α → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hfa : section5_SynthesisBound μ f 1)
    (hfg : section5_SynthesisBound μ (fun i x => f i x-g i x) δ) (n : ℕ) :
    section5_SynthesisBound (Measure.pi (fun _ : Fin n => μ))
      (fun a x => section5_tensor_family f n a x-section5_tensor_family g n a x)
      ((1+δ)^n-1) := by sorry
