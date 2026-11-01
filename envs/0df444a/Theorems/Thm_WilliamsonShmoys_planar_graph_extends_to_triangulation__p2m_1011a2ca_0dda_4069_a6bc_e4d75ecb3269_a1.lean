-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_extends_to_triangulation__p2m_1011a2ca_0dda_4069_a6bc_e4d75ecb3269_a1
-- name    : WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_1011a2ca_0dda_4069_a6bc_e4d75ecb3269_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:23:38.092708+00:00
-- url     : https://prove2.me/theorems/affb71eb-e232-4b0d-805e-31ff149cd3a9
-- title:
--   Extend a drawable graph to a triangulation
-- statement:
--   Every drawable simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges. The intended construction extends the drawing to a triangulation; Euler’s formula gives its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_1011a2ca_0dda_4069_a6bc_e4d75ecb3269_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
