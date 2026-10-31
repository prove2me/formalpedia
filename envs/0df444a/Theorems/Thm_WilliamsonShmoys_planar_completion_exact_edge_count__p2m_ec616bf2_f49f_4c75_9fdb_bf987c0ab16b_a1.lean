-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_exact_edge_count__p2m_ec616bf2_f49f_4c75_9fdb_bf987c0ab16b_a1
-- name    : WilliamsonShmoys.planar_completion_exact_edge_count__p2m_ec616bf2_f49f_4c75_9fdb_bf987c0ab16b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:32:49.62204+00:00
-- url     : https://prove2.me/theorems/e7b99952-d0a7-4658-9396-b1a5968fd530
-- title:
--   Exact edge-count completion of a drawable graph
-- statement:
--   Any drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_exact_edge_count__p2m_ec616bf2_f49f_4c75_9fdb_bf987c0ab16b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ N : SimpleGraph V,
      K.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
