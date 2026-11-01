-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_edge_count__p2m_33d20c1e_677c_47dc_9e82_8d3a28e57fca_a1
-- name    : WilliamsonShmoys.planar_extension_edge_count__p2m_33d20c1e_677c_47dc_9e82_8d3a28e57fca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:49:58.484127+00:00
-- url     : https://prove2.me/theorems/8c081704-c431-4561-a79b-9bf3229669d7
-- title:
--   Planar extension with exact maximal edge count
-- statement:
--   Every finitely drawable planar simple graph on at least three vertices has a planar supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_edge_count__p2m_33d20c1e_677c_47dc_9e82_8d3a28e57fca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
