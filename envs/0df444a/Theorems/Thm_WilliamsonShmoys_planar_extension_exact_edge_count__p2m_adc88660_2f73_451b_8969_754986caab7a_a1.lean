-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_exact_edge_count__p2m_adc88660_2f73_451b_8969_754986caab7a_a1
-- name    : WilliamsonShmoys.planar_extension_exact_edge_count__p2m_adc88660_2f73_451b_8969_754986caab7a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:20:25.167059+00:00
-- url     : https://prove2.me/theorems/f90d547e-0d6a-4173-8130-3021addb1efb
-- title:
--   Exact edge count for a planar supergraph
-- statement:
--   Any drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_extension_exact_edge_count__p2m_adc88660_2f73_451b_8969_754986caab7a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
