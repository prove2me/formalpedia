-- Prove2me | Theorems.Thm_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add
-- name    : contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/9f847e3f-b653-5632-8338-1c583488945b
-- title:
--   Smoothness and derivative bound for x-derivative slices
-- statement:
--   Let $n$ be a natural number and let $\Phi:\mathbb{R}\times(\mathrm{Fin}\,n\to\mathbb{R})\to\mathbb{C}$ be a function which is $C^\infty$ over $\mathbb{R}$ (smoothness of order $\top$ in $\mathbb{N}_\infty$); fix $j\in\mathbb{N}$ and $x\in\mathbb{R}$. Consider the slice function $g$ sending $y'\in(\mathrm{Fin}\,n\to\mathbb{R})$ to $\mathrm{iteratedDeriv}\,j\,(t\mapsto\Phi(t,y'))\,x$, that is, the $j$-th derivative in the first variable of $\Phi$, taken at the point $x$, with the second variable frozen at $y'$. The conclusion is a conjunction: first, $g$ is $C^\infty$ over $\mathbb{R}$ on $(\mathrm{Fin}\,n\to\mathbb{R})$; second, for every $N\in\mathbb{N}$ and every $y\in(\mathrm{Fin}\,n\to\mathbb{R})$, the norm of the $N$-th iterated Fréchet derivative of $g$ at $y$, as a continuous multilinear map, is at most the norm of the $(N+j)$-th iterated Fréchet derivative of $\Phi$ at the point $(x,y)$. Thus the bound holds with constant $1$, uniformly in $N$ and $y$.
--
--   This is the quantitative slicing estimate for a smooth function of one real variable and $n$ further real variables: partial differentiation $j$ times in the first variable and restriction to the slice costs nothing in operator norm beyond shifting the order of the total derivative by $j$. It is used in the construction of smooth bounds for derivatives of oscillatory integrals, feeding [`MeasureTheory.exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff`](thm.html#MeasureTheory.exists_forall_contDiff_norm_iteratedDeriv_integral_cexp_mul_le_prod_of_contDiff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add
    {n : ℕ} (Φ : ℝ × (Fin n → ℝ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (j : ℕ) (x : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) ∧
    ∀ (N : ℕ) (y : Fin n → ℝ),
      ‖iteratedFDeriv ℝ N (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) y‖ ≤
        ‖iteratedFDeriv ℝ (N + j) Φ (x, y)‖ := by sorry
