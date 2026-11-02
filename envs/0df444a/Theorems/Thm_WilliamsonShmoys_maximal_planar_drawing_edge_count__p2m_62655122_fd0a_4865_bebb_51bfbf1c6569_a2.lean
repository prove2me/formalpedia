-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:51:18.507191+00:00
-- url     : https://prove2.me/theorems/401105e3-1529-4fdd-958a-7e12d53ff038
-- title:
--   A maximal drawn planar graph has the triangulation edge count
-- statement:
--   A graph on at least three vertices that admits the specified planar drawing and has no strictly larger drawn supergraph on the same vertex type has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, HasPlanarDrawingOn N → M ≤ N → N = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card) = 3 * Fintype.card V - 6 := by sorry
