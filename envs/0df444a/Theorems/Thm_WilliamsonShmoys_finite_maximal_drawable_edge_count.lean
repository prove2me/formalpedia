-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_edge_count
-- name    : WilliamsonShmoys.finite_maximal_drawable_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:09:56.191449+00:00
-- url     : https://prove2.me/theorems/54cf9ee5-3148-49ab-8534-0945199afa08
-- title:
--   A maximal drawable graph has the planar bound edge count
-- statement:
--   If a drawable simple graph on at least three vertices has no proper drawable supergraph on the same vertex set, it has exactly 3|V|−6 edges. The independent proof route is to show that maximality forces a triangulation, establish the planar Euler relation for the resulting drawing, and count each triangular face on its three boundary edges. This child carries the geometric and Euler-formula work left by the parent reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_drawable_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ T : SimpleGraph V,
      (∀ {u v}, S.Adj u v → T.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    S.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
