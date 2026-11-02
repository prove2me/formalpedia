-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangulated_edge_count__p2m_b6ab3cff_6690_4a88_8301_64964a0bb841_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_b6ab3cff_6690_4a88_8301_64964a0bb841_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:49:54.856722+00:00
-- url     : https://prove2.me/theorems/1634faf2-3284-496c-bfc9-f8ff236eda71
-- title:
--   Planar supergraph with triangulated edge count
-- statement:
--   Every finite drawable graph on at least three vertices has a drawable supergraph on the same vertex type with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_b6ab3cff_6690_4a88_8301_64964a0bb841_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       letI : Fintype ↑L.edgeSet := Fintype.ofFinite _
       3 * Fintype.card V = L.edgeFinset.card + 6) := by sorry
