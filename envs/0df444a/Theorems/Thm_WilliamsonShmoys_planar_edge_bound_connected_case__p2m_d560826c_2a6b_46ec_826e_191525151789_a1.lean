-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected_case__p2m_d560826c_2a6b_46ec_826e_191525151789_a1
-- name    : WilliamsonShmoys.planar_edge_bound_connected_case__p2m_d560826c_2a6b_46ec_826e_191525151789_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:39:19.457246+00:00
-- url     : https://prove2.me/theorems/5d7de761-00c1-4894-a578-f11ed0ef9fe3
-- title:
--   Planar edge bound in the connected case
-- statement:
--   For a connected graph with at least three vertices, the local induced-subgraph bound applied to the full vertex set gives the global edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_connected_case__p2m_d560826c_2a6b_46ec_826e_191525151789_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hcard : 3 <= Fintype.card V)
    (hlocal : ∀ s : Finset V, 3 <= s.card →
      (N.induce (s : Set V)).Connected →
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6)
    (hconn : N.Connected) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
