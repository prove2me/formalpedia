-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_augmentation
-- name    : WilliamsonShmoys.exists_planar_edge_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:39:59.60244+00:00
-- url     : https://prove2.me/theorems/763b388f-d64b-4f62-8af1-3391fd90b369
-- title:
--   Add an edge between components of a planar drawing
-- statement:
--   A disconnected graph on at least three vertices with the given crossing-free drawing has a strictly larger simple graph on the same vertices that still has a crossing-free drawing. The strict extension supplies at least one new edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
