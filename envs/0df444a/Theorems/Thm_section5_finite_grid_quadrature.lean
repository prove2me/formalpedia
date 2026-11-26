-- Prove2me | Theorems.Thm_section5_finite_grid_quadrature
-- name    : section5_finite_grid_quadrature
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:20:08.921778+00:00
-- url     : https://prove2.me/theorems/9a5ae73b-d162-4b0a-bbef-41338ca5c2b6
-- title:
--   Exact quadrature for a cell-constant grid function
-- statement:
--   Let $n,N\in\mathbb N$, $a\in\mathbb R$, and $\delta>0$. Define $r(x)=a+\delta\lfloor(x-a)/\delta\rfloor$ and apply it coordinatewise. For every measurable $F:\mathbb R^n\to\mathbb C$,
--
--   $$\int_{[a,a+N\delta)^n}F(r(x))\,dx=\delta^n\sum_{j\in\{0,\ldots,N-1\}^n}F(a+\delta j).$$
--
--   This is the exact correspondence between finite grid sums and integrals of their piecewise constant lifts.
-- source:
--   Original grid-measure auxiliary result supporting Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D. Formalization: Solutions/Section5FiniteGridMeasure.lean, lines 79–93.

import Definitions.Def_Section5Verified_Section5CellQuadrature
import Definitions.Def_Section5Verified_Section5FiniteGridMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set

theorem section5_finite_grid_quadrature (n N : ℕ) (a δ : ℝ) (hδ : 0 < δ)
    (F : (Fin n → ℝ) → ℂ) (hF : Measurable F) :
    (∫ x, F (fun i => section5_grid_sample a δ (x i))
      ∂(Measure.pi (fun _ : Fin n => volume.restrict (Ico a (a+N*δ))))) =
      (δ^n : ℂ) * ∑ j : Fin n → Fin N, F (fun i => a+(j i:ℝ)*δ) := by sorry
