-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_extension__p2m_e657dedf_589f_4338_b1cf_3cbd004df18d_a1
-- name    : WilliamsonShmoys_edge_maximal_planar_extension__p2m_e657dedf_589f_4338_b1cf_3cbd004df18d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T01:01:13.192649+00:00
-- url     : https://prove2.me/theorems/06c1ed51-7563-4611-8e64-26f357d4899b
-- title:
--   Edge-maximal planar extension on the same vertices
-- statement:
--   Every connected finite planar simple graph on at least three vertices has a connected, edge-maximal planar supergraph on the same vertex set, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys_edge_maximal_planar_extension__p2m_e657dedf_589f_4338_b1cf_3cbd004df18d_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K.Connected ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
