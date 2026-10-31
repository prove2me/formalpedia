-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:57.73644+00:00
-- url     : https://prove2.me/theorems/4bcdc3e6-0270-418b-8eb0-da52e5830988
-- title:
--   Planar edge-count upper bound
-- statement:
--   Any finite simple graph drawable under the supplied crossing-free drawing predicate, with at least three vertices, has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
