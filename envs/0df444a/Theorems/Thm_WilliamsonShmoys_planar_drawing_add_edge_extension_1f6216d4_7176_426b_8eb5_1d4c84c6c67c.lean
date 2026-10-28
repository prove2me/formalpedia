-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- name    : WilliamsonShmoys.planar_drawing_add_edge_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:13:24.831502+00:00
-- url     : https://prove2.me/theorems/11f67c28-921f-4477-bb91-70b761f9814a
-- title:
--   Strict planar extension of a disconnected drawing
-- statement:
--   Every disconnected finite graph with a drawing as defined in `HasPlanarDrawingOn` has a strictly larger drawn supergraph on the same vertices. Since the drawing is existential, the proof may redraw its components before adding a bridge; it need not preserve a supplied placement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hnotconn : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        G.edgeSet.ncard < K.edgeSet.ncard := by
  sorry
