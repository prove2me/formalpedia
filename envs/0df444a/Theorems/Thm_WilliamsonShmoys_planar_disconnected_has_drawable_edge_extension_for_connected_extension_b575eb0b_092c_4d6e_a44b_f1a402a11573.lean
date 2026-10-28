-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_drawable_edge_extension_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573
-- name    : WilliamsonShmoys.planar_disconnected_has_drawable_edge_extension_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T18:13:57.576189+00:00
-- url     : https://prove2.me/theorems/298a744f-4801-4a25-98ed-29f3a47f4c54
-- title:
--   A disconnected drawable graph has a strict drawable extension
-- statement:
--   Every disconnected drawable graph has a strict drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_disconnected_has_drawable_edge_extension_for_connected_extension_b575eb0b_092c_4d6e_a44b_f1a402a11573
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hDisconnected : ¬ K.Connected) :
    ∃ N : SimpleGraph V,
      K ≤ N ∧ K ≠ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N := by sorry
