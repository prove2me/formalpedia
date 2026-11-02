-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_2120accc_e77c_4707_8c72_d7b3ece39068_a1
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_2120accc_e77c_4707_8c72_d7b3ece39068_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:42:38.439134+00:00
-- url     : https://prove2.me/theorems/6467164a-4ac7-4202-bbd8-0cd7677d3ce4
-- title:
--   Planar triangulated supergraph with the same vertices
-- statement:
--   Any graph on at least three vertices with the specified planar drawing is contained, on the same vertex type, in a graph with a planar drawing and exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_2120accc_e77c_4707_8c72_d7b3ece39068_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     ∃ H : SimpleGraph V,
       N ≤ H ∧
       WilliamsonShmoys.HasPlanarDrawingOn H ∧
       (letI : DecidableRel H.Adj := Classical.decRel H.Adj
        H.edgeFinset.card + 6 = 3 * Fintype.card V)) := by sorry
