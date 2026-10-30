-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_172ec1a1_67dd_48ed_9b1c_20de26385b63_a1
-- name    : WilliamsonShmoys.planar_supergraph_triangulation__p2m_172ec1a1_67dd_48ed_9b1c_20de26385b63_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:45.795529+00:00
-- url     : https://prove2.me/theorems/860d3bdd-f3ca-4e9c-8e9b-5739b7876622
-- title:
--   Triangulating planar supergraph on the same vertices
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertices whose edge count is exactly 3|V| − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation__p2m_172ec1a1_67dd_48ed_9b1c_20de26385b63_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
