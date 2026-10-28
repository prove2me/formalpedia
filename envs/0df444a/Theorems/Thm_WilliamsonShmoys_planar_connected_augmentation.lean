-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_augmentation
-- name    : WilliamsonShmoys.planar_connected_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:49:51.127988+00:00
-- url     : https://prove2.me/theorems/6c12478a-58d5-4cf0-93dc-a04ced5ee05e
-- title:
--   Connected planar augmentation of a disconnected planar graph
-- statement:
--   If a graph has a crossing-free drawing and two vertices lie in different components, it has a strict connected planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V} (hUnreachable : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ G ≠ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
