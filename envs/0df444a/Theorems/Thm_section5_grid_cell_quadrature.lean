-- Prove2me | Theorems.Thm_section5_grid_cell_quadrature
-- name    : section5_grid_cell_quadrature
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:04:02.114989+00:00
-- url     : https://prove2.me/theorems/2dcd1fd0-1799-5da5-87b7-b431a3157fc6
-- title:
--   Uniform-cell sampling error from derivative energy
-- statement:
--   Let $E$ be a real Banach space and let $f,g:\mathbb R\to E$ satisfy $f'(x)=g(x)$ for every $x$, with $g$ continuous. For $a\in\mathbb R$, a cell width $\delta\ge0$, and $N\in\mathbb N$,
--
--   $$\sum_{j=0}^{N-1}\int_{a+j\delta}^{a+(j+1)\delta}\|f(x)-f(a+j\delta)\|^2\,dx\le\delta^2\int_a^{a+N\delta}\|g(y)\|^2\,dy.$$
--
--   This gives a sampling estimate for the piecewise constant approximation on a uniform grid, including zero-width and empty-grid cases.
-- source:
--   Original analytic auxiliary result for the sampling argument in Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D. Formalization: Solutions/Section5CellQuadrature.lean, lines 152–176.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set

theorem section5_grid_cell_quadrature {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f g : ℝ → E)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (a δ : ℝ) (hδ : 0 ≤ δ) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      ∫ x in (a+j*δ)..(a+(j+1)*δ), ‖f x-f (a+j*δ)‖^2) ≤
      δ^2 * ∫ y in a..(a+N*δ), ‖g y‖^2 := by sorry
