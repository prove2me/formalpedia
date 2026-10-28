-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_strict_supergraph
-- name    : WilliamsonShmoys.planar_disconnected_has_strict_supergraph
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T06:09:46.684116+00:00
-- url     : https://prove2.me/theorems/0d10ba9f-0156-4090-a93d-bd4a819572ba
-- title:
--   A disconnected plane graph admits a strict planar extension
-- statement:
--   Every disconnected finite graph with the specified crossing-free drawing has a strictly larger graph on the same vertices that also has such a drawing. A proof can connect two components by an arc lying in a face incident to both, then add the resulting edge. This isolates the geometric step; it does not assume a connected augmentation result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_has_strict_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
