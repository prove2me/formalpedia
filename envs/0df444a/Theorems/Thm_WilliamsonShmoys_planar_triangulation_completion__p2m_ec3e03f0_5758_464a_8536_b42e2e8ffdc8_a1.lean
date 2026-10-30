-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_ec3e03f0_5758_464a_8536_b42e2e8ffdc8_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_ec3e03f0_5758_464a_8536_b42e2e8ffdc8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:27:17.387489+00:00
-- url     : https://prove2.me/theorems/93ac3156-1efb-4b4a-874e-65a14cba6456
-- title:
--   Triangulated completion of a drawable graph
-- statement:
--   Any drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_ec3e03f0_5758_464a_8536_b42e2e8ffdc8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ P : SimpleGraph V, G ≤ P ∧ HasPlanarDrawingOn P ∧
      P.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
