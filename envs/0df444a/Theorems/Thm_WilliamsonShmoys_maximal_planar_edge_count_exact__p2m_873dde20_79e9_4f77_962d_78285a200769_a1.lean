-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_exact__p2m_873dde20_79e9_4f77_962d_78285a200769_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_exact__p2m_873dde20_79e9_4f77_962d_78285a200769_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:48:32.489089+00:00
-- url     : https://prove2.me/theorems/97299b19-436d-416a-9d25-459f10ba4ac7
-- title:
--   Exact edge count for a maximal finite planar graph
-- statement:
--   A finite simple graph on at least three vertices that has a crossing-free drawing and is maximal among drawable supergraphs on the same vertex set has exactly 3|V| − 6 edges. This child captures the triangulation and Euler-counting argument; it is stronger than the requested lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_exact__p2m_873dde20_79e9_4f77_962d_78285a200769_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T) (hMax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : 3 * Fintype.card V = T.edgeSet.ncard + 6 := by sorry
