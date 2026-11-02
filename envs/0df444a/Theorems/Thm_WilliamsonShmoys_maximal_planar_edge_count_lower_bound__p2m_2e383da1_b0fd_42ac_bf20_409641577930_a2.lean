-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:45:12.241002+00:00
-- url     : https://prove2.me/theorems/3c4a1050-73ac-4fb0-b659-1aa33a199ba4
-- title:
--   A maximal planar drawing has at least three n minus six edges
-- statement:
--   A graph on at least three vertices that has a drawing satisfying HasPlanarDrawingOn and is maximal among drawable supergraphs on the same vertex type has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by sorry
