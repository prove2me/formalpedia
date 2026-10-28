-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_edge_extension
-- name    : WilliamsonShmoys.planar_drawing_disconnected_edge_extension
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-25T23:46:20.662771+00:00
-- url     : https://prove2.me/theorems/77ddbab4-d3b2-448d-9101-2056dc3e4630
-- title:
--   Planar edge augmentation for disconnected drawn graphs
-- statement:
--   Every disconnected finite graph with the specified planar drawing has a proper planar supergraph on the same vertices. This is the geometric augmentation step; the parent follows by applying maximality to K and contradicting ¬ K ≤ H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_disconnected_edge_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hDisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ¬ K ≤ H := by
  sorry
