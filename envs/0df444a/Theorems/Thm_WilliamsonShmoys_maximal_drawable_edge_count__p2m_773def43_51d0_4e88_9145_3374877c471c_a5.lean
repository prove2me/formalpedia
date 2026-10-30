-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:44:12.917017+00:00
-- url     : https://prove2.me/theorems/eb21a977-2509-4ef4-8e83-e4c522788ebf
-- title:
--   Exact edge count of a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has edge count exactly 3|V|−6, expressed without subtraction. A proof route first establishes connectedness and triangular faces from maximality, then applies Euler’s formula and counts face-edge incidences. This isolates the main topological obligation; the parent uses the equality only after extending its graph to a maximal drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
