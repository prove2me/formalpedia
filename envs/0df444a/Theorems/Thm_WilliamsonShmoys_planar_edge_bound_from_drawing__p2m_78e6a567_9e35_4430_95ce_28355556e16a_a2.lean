-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
-- name    : WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:22:32.250217+00:00
-- url     : https://prove2.me/theorems/45533a44-b035-4e47-8a66-77352d0d9780
-- title:
--   The simple planar edge bound
-- statement:
--   A connected simple planar graph on at least three vertices has at most 3n − 6 edges. One proof route extends the drawing to a maximal simple plane graph on the same vertices, whose faces are triangular. Combined with the Euler child, this removes the requested face-boundary inequality from the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
