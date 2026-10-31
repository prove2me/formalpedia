-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_4c578d9c_5ad8_4ad5_bf9f_68265b93ec4b_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_4c578d9c_5ad8_4ad5_bf9f_68265b93ec4b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:50:55.369988+00:00
-- url     : https://prove2.me/theorems/ea884ca3-04a5-4dba-9b23-69a847b241a6
-- title:
--   Maximality forces the triangulation edge lower bound
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable supergraph inclusion has at least three times its number of vertices minus six edges. A proof route is to show maximality forces connectedness and then a triangulation, including the small and disconnected cases, and count triangular faces using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_4c578d9c_5ad8_4ad5_bf9f_68265b93ec4b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
