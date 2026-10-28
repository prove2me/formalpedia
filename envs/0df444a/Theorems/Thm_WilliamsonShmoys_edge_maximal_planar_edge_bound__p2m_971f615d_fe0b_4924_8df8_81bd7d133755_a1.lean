-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_bound__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_bound__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:05:56.669499+00:00
-- url     : https://prove2.me/theorems/ca4f62b0-0fc3-4b70-a0ef-3ca6355feff9
-- title:
--   Edge bound for an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges. The proof route is to establish connectedness and triangular faces from maximality, then use Euler’s formula and count face-edge incidences; the |V|=3 boundary case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.edge_maximal_planar_edge_bound__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
