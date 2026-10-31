-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_connected_edge_count_lower_bound__p2m_3e960d88_24fa_4e6d_b367_13e60076bdee_a1
-- name    : WilliamsonShmoys.finite_connected_edge_count_lower_bound__p2m_3e960d88_24fa_4e6d_b367_13e60076bdee_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:46:50.664239+00:00
-- url     : https://prove2.me/theorems/94112ea2-bda9-44b5-b77c-78dc5343ca28
-- title:
--   Edge lower bound for a finite connected graph
-- statement:
--   Every finite connected graph has at least one fewer edge than vertices. This isolates the graph-theoretic counting step needed by the parent; it does not require a drawing or linear order.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_connected_edge_count_lower_bound__p2m_3e960d88_24fa_4e6d_b367_13e60076bdee_a1
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hconn : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 := by
  sorry
