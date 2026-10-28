-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension
-- name    : WilliamsonShmoys.planar_drawing_connected_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:33:09.24989+00:00
-- url     : https://prove2.me/theorems/c67fb017-3bd0-4151-a43a-5ab17d8c263e
-- title:
--   Extend a drawn planar graph to a connected planar supergraph
-- statement:
--   Any finite drawn planar simple graph on at least three vertices has a connected planar simple supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧ H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
