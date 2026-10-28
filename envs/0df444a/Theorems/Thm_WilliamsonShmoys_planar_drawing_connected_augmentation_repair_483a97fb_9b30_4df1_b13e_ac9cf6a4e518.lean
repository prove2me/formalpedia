-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:10:08.005658+00:00
-- url     : https://prove2.me/theorems/21668f8b-47f2-43f2-9d10-1a4cb968509f
-- title:
--   Connected planar augmentation with a vertex bound
-- statement:
--   On a finite vertex type with at least three vertices, a graph having the supplied planar drawing can be augmented to a connected graph on the same vertices, preserving a planar drawing and every original edge. The edge-count inequality makes the augmentation useful for the parent bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      H.Connected ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
