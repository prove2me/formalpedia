-- Prove2me | Theorems.Thm_intervalIntegral_iteratedFDeriv_integral_of_contDiff
-- name    : intervalIntegral.iteratedFDeriv_integral_of_contDiff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:31:19.422891+00:00
-- url     : https://prove2.me/theorems/f089b069-762c-4fad-9dbc-65a1bac11b39
-- title:
--   Higher derivatives of a smooth parametric integral over $[0,1]$
-- statement:
--   Let $H$ be a finite-dimensional real normed space, $G$ a real Banach space, and $F:H\times\mathbb R\to G$, $(x,t)\mapsto F(x,t)$, a $C^\infty$ map. Then for every $k\in\mathbb N$ and every $x\in H$,
--   $$D^k\Big(x\mapsto\int_0^1F(x,t)\,dt\Big)(x)=\int_0^1D^k_xF(x,t)\,dt,$$
--   an identity of continuous $k$-linear maps $H^k\to G$.
--
--   This is the iterated form of differentiation under the integral sign for smooth parametric integrals over a compact interval; it complements the published smoothness and norm-bound statements for the same integral.
--
--   Formalization Note: `F : H → ℝ → G` with `ContDiff ℝ ∞ (Function.uncurry F)`; the conclusion is an equality of functions `H → ContinuousMultilinearMap ℝ (fun _ : Fin k => H) G`, using `iteratedFDeriv ℝ k` and the interval integral `∫ t in (0 : ℝ)..1`.
-- source:
--   Standard (differentiation under the integral sign, iterated)

import Mathlib

namespace intervalIntegral

open scoped ContDiff

/-- Let `H` be a finite-dimensional real normed space, `G` a real Banach space and
`F : H → ℝ → G` jointly `C^∞`. Then for every `k`, the `k`-th Fréchet derivative of
`x ↦ ∫ t in 0..1, F x t` is `x ↦ ∫ t in 0..1, D^k_x F x t`. -/
theorem iteratedFDeriv_integral_of_contDiff {H G : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {F : H → ℝ → G} (hF : ContDiff ℝ ∞ (Function.uncurry F)) (k : ℕ) :
    (fun x => iteratedFDeriv ℝ k (fun x => ∫ t in (0 : ℝ)..1, F x t) x) =
      fun x => ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (fun x => F x t) x := by
  sorry

end intervalIntegral
