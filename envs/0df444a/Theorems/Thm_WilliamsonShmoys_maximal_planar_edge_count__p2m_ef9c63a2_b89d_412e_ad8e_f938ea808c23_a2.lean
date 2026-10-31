-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:10:26.888988+00:00
-- url     : https://prove2.me/theorems/4c578d9c-5ad8-4ad5-bf9f-68265b93ec4b
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable supergraph inclusion on the same vertex type has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
