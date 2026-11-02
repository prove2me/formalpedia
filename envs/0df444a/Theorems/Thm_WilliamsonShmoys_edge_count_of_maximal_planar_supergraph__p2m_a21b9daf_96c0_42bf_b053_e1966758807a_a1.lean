-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_supergraph__p2m_a21b9daf_96c0_42bf_b053_e1966758807a_a1
-- name    : WilliamsonShmoys_edge_count_of_maximal_planar_supergraph__p2m_a21b9daf_96c0_42bf_b053_e1966758807a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:59:48.576171+00:00
-- url     : https://prove2.me/theorems/6bb0623d-4ea1-4aa8-a0da-a55490a47412
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A connected, inclusion-maximal finite simple graph on at least three vertices that admits a drawing satisfying HasPlanarDrawingOn has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys_edge_count_of_maximal_planar_supergraph__p2m_a21b9daf_96c0_42bf_b053_e1966758807a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
