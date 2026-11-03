-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulating_supergraph__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulating_supergraph__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:43:44.359972+00:00
-- url     : https://prove2.me/theorems/bf9cfcbc-5b59-49b9-abb2-d36aa9cb22f2
-- title:
--   Triangulating planar supergraph on the same vertices
-- statement:
--   Any graph with the stated crossing-free drawing and at least three vertices is a subgraph of a graph on the same vertices that has such a drawing and exactly $3|V|-6$ edges. The vertex lower bound is needed for the triangulation edge formula; no connectedness assumption is imposed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulating_supergraph__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card) = 3 * Fintype.card V - 6 := by sorry
