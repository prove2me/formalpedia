-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:03:20.719315+00:00
-- url     : https://prove2.me/theorems/adc88660-2f73-451b-8969-754986caab7a
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = N.edgeSet) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
