-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:53.222277+00:00
-- url     : https://prove2.me/theorems/e16fd743-6daf-4b1b-8baa-fc8319a376a6
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph with at least three vertices and no strictly larger drawable supergraph on the same vertex set has exactly 3|V| − 6 edges. The proof route is to show maximality forces a connected triangulation, then apply Euler’s formula; at three vertices the conclusion is three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2 {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
