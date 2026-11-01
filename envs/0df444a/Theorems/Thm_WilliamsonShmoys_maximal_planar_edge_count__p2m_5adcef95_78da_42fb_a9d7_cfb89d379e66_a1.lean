-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:11.736759+00:00
-- url     : https://prove2.me/theorems/6ecf0cee-d9a3-4304-bd4e-76be40fa28fb
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   A finite drawable simple graph with at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ H : SimpleGraph V, L ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
