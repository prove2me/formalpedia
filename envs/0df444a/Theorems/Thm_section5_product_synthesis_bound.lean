-- Prove2me | Theorems.Thm_section5_product_synthesis_bound
-- name    : section5_product_synthesis_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:29.757934+00:00
-- url     : https://prove2.me/theorems/300e9873-fd66-4215-a19e-a30181c21e57
-- title:
--   Product-space synthesis bounds multiply
-- statement:
--   Let μ,ν be s-finite measures, I,J finite, and f_i∈L²(μ), g_j∈L²(ν) be complex families. Suppose their squared synthesis integrals are bounded by A²Σ_i|a_i|² and B²Σ_j|b_j|², respectively, for every coefficient vector, with A,B real. Then every complex array c_ij satisfies $$\int\left|\sum_{i,j}c_{ij}f_i(x)g_j(y)\right|^2d(\mu\otimes\nu)(x,y)\le(AB)^2\sum_{i,j}|c_{ij}|^2.$$ The coefficient array need not factor as a product.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5ProductSampling.lean, lines 66–76. Analytic context: Section 5.1, Lemma 5.1 and Appendix D; this auxiliary formulation does not assert the main quantum learning algorithm.

import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem section5_product_synthesis_bound {α β ι κ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Fintype ι] [Fintype κ]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (f : ι → α → ℂ) (g : κ → β → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ j, MemLp (g j) 2 ν)
    (A B : ℝ)
    (hA : ∀ c : ι → ℂ, (∫ x, ‖∑ i, c i*f i x‖^2 ∂μ) ≤ A^2*∑ i, ‖c i‖^2)
    (hB : ∀ c : κ → ℂ, (∫ y, ‖∑ j, c j*g j y‖^2 ∂ν) ≤ B^2*∑ j, ‖c j‖^2)
    (c : ι → κ → ℂ) :
    (∫ z : α×β, ‖∑ i, ∑ j, c i j*f i z.1*g j z.2‖^2 ∂(μ.prod ν)) ≤
      (A*B)^2*∑ i, ∑ j, ‖c i j‖^2 := by sorry
