-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_add_edge_when_disconnected
-- name    : WilliamsonShmoys.planar_graph_add_edge_when_disconnected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:25:27.446782+00:00
-- url     : https://prove2.me/theorems/2d79a091-ef79-41d3-a17f-b65da239aa65
-- title:
--   Add an edge between components of a drawable graph
-- statement:
--   If a drawable finite graph has at least three vertices and is disconnected, it has a drawable supergraph on the same vertices with strictly more edges, obtained by joining two components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_add_edge_when_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        H.edgeSet.ncard < K.edgeSet.ncard := by sorry
