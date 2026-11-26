-- Prove2me | Theorems.Thm_section5_grid_sampling_integral
-- name    : section5_grid_sampling_integral
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:04:15.583487+00:00
-- url     : https://prove2.me/theorems/23ec0988-be04-500f-a910-9aa2939c09be
-- title:
--   Uniform-grid sampling error decomposes into cell integrals
-- statement:
--   Let E be a normed additive commutative group and f:R→E continuous. Let a be real, δ>0 and N natural, and define the left-grid sampling map R(x)=a+δ⌊(x−a)/δ⌋. For Lebesgue interval integrals,
--
--   $$\int_a^{a+N\delta}\|f(x)-f(R(x))\|^2\,dx=\sum_{j=0}^{N-1}\int_{a+j\delta}^{a+(j+1)\delta}\|f(x)-f(a+j\delta)\|^2\,dx.$$
--
--   The equality includes an empty grid N=0.
-- source:
--   Original analytic auxiliary identity supporting the discretization analysis in Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1. Exact formalization: Solutions/Section5CellQuadrature.lean, lines 45–50; sampling map, lines 7–8.

import Definitions.Def_Section5Verified_Section5CellQuadrature
import Mathlib
set_option autoImplicit false
open MeasureTheory Set

theorem section5_grid_sampling_integral {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) (a δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    (∫ x in a..(a+N*δ), ‖f x-f (section5_grid_sample a δ x)‖^2) =
      ∑ j ∈ Finset.range N,
        ∫ x in (a+j*δ)..(a+(j+1)*δ), ‖f x-f (a+j*δ)‖^2 := by sorry
