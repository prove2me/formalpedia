-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:48:59.537159+00:00
-- url     : https://prove2.me/theorems/754c9e67-063f-454f-af82-f5a72bd27cdb
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Every drawable finite graph on at least three vertices is a subgraph of a drawable graph on the same vertex type whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, M ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
        3 * Fintype.card V = K.edgeFinset.card + 6) := by sorry
