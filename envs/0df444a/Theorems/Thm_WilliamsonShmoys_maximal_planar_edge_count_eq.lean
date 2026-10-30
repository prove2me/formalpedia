-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq
-- name    : WilliamsonShmoys.maximal_planar_edge_count_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:34:51.129267+00:00
-- url     : https://prove2.me/theorems/bd64bb67-a527-47f5-b6f5-f9cc0e8303f4
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A simple graph on at least three finite vertices that has a crossing-free drawing and is maximal among graphs on those vertices with such a drawing has exactly 3|V|−6 edges, expressed without truncated subtraction as edge count plus six equals three times the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_eq
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N → WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
