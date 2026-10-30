-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:32:13.730116+00:00
-- url     : https://prove2.me/theorems/760d336b-8795-40bc-8413-7180f98d62aa
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A connected simple graph with a planar drawing on at least three vertices, maximal among planar supergraphs on the same vertex set, has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      (letI : DecidableRel L.Adj := dL
       H ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ H))
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
