-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count__p2m_c2eda16e_e381_4c67_86d8_74bdc260bd3a_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_c2eda16e_e381_4c67_86d8_74bdc260bd3a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:20:42.780864+00:00
-- url     : https://prove2.me/theorems/0c9ddbae-e05c-4655-8aee-21825ef9cfbc
-- title:
--   Planar drawing completion with triangulated edge count
-- statement:
--   Any drawable simple graph on a finite ordered vertex set of size at least three has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_c2eda16e_e381_4c67_86d8_74bdc260bd3a_a1 {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
