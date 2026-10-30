-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_exact_edge_count__p2m_85349ab1_c6ef_46c3_ac33_c15eeda728ae_a2
-- name    : WilliamsonShmoys.planar_completion_exact_edge_count__p2m_85349ab1_c6ef_46c3_ac33_c15eeda728ae_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:29:11.53806+00:00
-- url     : https://prove2.me/theorems/0b759ff7-c54c-46d9-9040-98bf9ecec633
-- title:
--   Planar completion with exact maximal edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices can be extended on the same vertex set to a drawable graph with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_exact_edge_count__p2m_85349ab1_c6ef_46c3_ac33_c15eeda728ae_a2 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
