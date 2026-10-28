-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_037368dd_04cc_4345_b537_96bdbb1ae146
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_037368dd_04cc_4345_b537_96bdbb1ae146
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:09:38.040893+00:00
-- url     : https://prove2.me/theorems/875ae99f-1c0b-40d1-b7d9-b20a973432c9
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite linearly ordered vertices that has no proper drawable supergraph on those vertices has exactly 3|V| − 6 edges. The proof route is to establish that maximality forces a triangulation, then apply Euler’s formula and count face-edge incidences. The bound of at least three vertices is necessary for this edge formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_037368dd_04cc_4345_b537_96bdbb1ae146
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
