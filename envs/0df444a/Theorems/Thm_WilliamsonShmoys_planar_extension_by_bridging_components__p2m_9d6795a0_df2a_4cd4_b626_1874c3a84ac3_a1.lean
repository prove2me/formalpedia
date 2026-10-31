-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_by_bridging_components__p2m_9d6795a0_df2a_4cd4_b626_1874c3a84ac3_a1
-- name    : WilliamsonShmoys.planar_extension_by_bridging_components__p2m_9d6795a0_df2a_4cd4_b626_1874c3a84ac3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:30:01.818594+00:00
-- url     : https://prove2.me/theorems/da8118fe-17fb-4c93-a2d6-08f851f61791
-- title:
--   Planar edge extension across disconnected components
-- statement:
--   Any disconnected graph with at least two vertices that has a crossing-free drawing admits a crossing-free supergraph on the same vertices containing at least one new edge. The independent proof route is to choose distinct connected components and extend their planar drawing by a bridge routed through the plane’s faces, preserving the existing arcs and vertex locations. This lemma supplies the topological work needed by the target; its cardinality boundary includes the two-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_extension_by_bridging_components__p2m_9d6795a0_df2a_4cd4_b626_1874c3a84ac3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : ¬ L.Connected)
    (hV : 2 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v, H.Adj u v ∧ ¬ L.Adj u v := by sorry
