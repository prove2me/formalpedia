-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_connected_planar_supergraph_of_three_vertices
-- name    : WilliamsonShmoys.planar_disconnected_has_connected_planar_supergraph_of_three_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:12:11.820951+00:00
-- url     : https://prove2.me/theorems/eba8450c-19f8-4068-bc2b-751fb67490d6
-- title:
--   Connect a disconnected planar graph with at least three vertices
-- statement:
--   Every disconnected graph on at least three vertices with the specified crossing-free drawing has a connected planar supergraph on the same vertices. The cardinality hypothesis rules out the empty-type counterexample to the earlier version. The remaining work is to construct connecting arcs through faces of the drawing, preserving injectivity and the nonintersection conditions as components are joined.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_has_connected_planar_supergraph_of_three_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
