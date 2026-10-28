-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:15:10.453539+00:00
-- url     : https://prove2.me/theorems/1949c49b-65df-4985-a3df-d15a4e963e8a
-- title:
--   Connecting a planar drawing without adding vertices
-- statement:
--   For a finite graph with the specified crossing-free drawing and at least three vertices, construct a walk-connected planar supergraph on the same vertex type, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
