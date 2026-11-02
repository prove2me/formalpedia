-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:02:27.093327+00:00
-- url     : https://prove2.me/theorems/fb63e52b-62b1-491c-ab5d-ee94b001efe6
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal planar simple graph on at least three vertices has exactly 3|V|−6 edges. This removes the edge-count obligation from the parent. A proof route is to show maximality forces connectedness and triangular faces, count incidences between faces and edges, and combine that count with Euler’s formula. At |V| = 3, the graph is K₃ and the equation holds. The face and incidence arguments for the supplied arc-based drawing predicate remain the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
