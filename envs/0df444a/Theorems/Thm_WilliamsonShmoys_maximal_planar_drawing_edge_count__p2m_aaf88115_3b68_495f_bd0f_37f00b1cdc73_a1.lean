-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:05:49.193282+00:00
-- url     : https://prove2.me/theorems/03ab0e36-fd73-4929-a651-a82d3a3cc822
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_aaf88115_3b68_495f_bd0f_37f00b1cdc73_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
