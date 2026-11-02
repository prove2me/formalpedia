-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a95b2e09_031c_4e18_b347_423c7cdf2425_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_a95b2e09_031c_4e18_b347_423c7cdf2425_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:37:29.426472+00:00
-- url     : https://prove2.me/theorems/dc6f4f47-fc7e-434e-bbbd-7ebe237d247e
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A connected graph on at least three vertices that has a planar drawing and is maximal among drawable supergraphs on the same vertex set has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_a95b2e09_031c_4e18_b347_423c7cdf2425_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hconn : J.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : ∀ K : SimpleGraph V, J ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    J.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
