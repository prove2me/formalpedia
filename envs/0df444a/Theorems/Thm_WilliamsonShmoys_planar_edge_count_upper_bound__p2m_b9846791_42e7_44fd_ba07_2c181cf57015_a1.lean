-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:42:54.174213+00:00
-- url     : https://prove2.me/theorems/0d510956-7da0-4290-84d6-372bf969c07f
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph with at least three vertices and a planar drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card + 6 <= 3 * Fintype.card V) := by sorry
