-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:22:34.423823+00:00
-- url     : https://prove2.me/theorems/edcdc3e6-c2e4-41fd-9c23-1e4fa303ea8c
-- title:
--   Maximal planar edge lower bound
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable supergraphs has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
