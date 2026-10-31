-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_edge_count__p2m_a3a14366_dd9a_40cc_8d47_64e2f5da9564_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_edge_count__p2m_a3a14366_dd9a_40cc_8d47_64e2f5da9564_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:47:23.284311+00:00
-- url     : https://prove2.me/theorems/10e3a5b8-1f49-4831-b4a7-c5e9b9512625
-- title:
--   Planar completion to a triangulated maximal supergraph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly 3|V|−6. This packages the topological completion, triangulation, Euler formula, and face-edge incidence argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_edge_count__p2m_a3a14366_dd9a_40cc_8d47_64e2f5da9564_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
