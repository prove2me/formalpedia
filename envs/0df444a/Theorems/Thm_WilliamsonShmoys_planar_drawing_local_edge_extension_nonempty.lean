-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_local_edge_extension_nonempty
-- name    : WilliamsonShmoys.planar_drawing_local_edge_extension_nonempty
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:09:08.637231+00:00
-- url     : https://prove2.me/theorems/ad1f13f5-2095-4f5f-9f18-0e76b27c008d
-- title:
--   Add an edge to a nonempty disconnected planar drawing
-- statement:
--   For a graph on at least three vertices with a planar drawing, if the graph is disconnected, it can be extended by at least one new edge while retaining a planar drawing. The cardinality hypothesis rules out empty and singleton vertex types and gives the augmentation lemma the target's size boundary explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_local_edge_extension_nonempty
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hNotConn : ¬ H.Connected) :
    ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∃ u v : V, L.Adj u v ∧ ¬ H.Adj u v := by sorry
