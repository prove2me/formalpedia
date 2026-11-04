-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:05:19.29624+00:00
-- url     : https://prove2.me/theorems/c3950eb8-41cb-4e65-a38c-065736da1c7d
-- title:
--   Planar graph edge-count upper bound
-- statement:
--   Every finite simple graph with at least three vertices and a planar drawing has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7bdfbc7b_3903_44da_a815_425149078ac6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  sorry
