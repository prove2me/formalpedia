-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_finite_maximal_extension
-- name    : WilliamsonShmoys.planar_augmentation_finite_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:58:39.148676+00:00
-- url     : https://prove2.me/theorems/5a324966-efa5-40f9-a8b3-6656a566ab19
-- title:
--   Finite maximal planar extension
-- statement:
--   A planar graph on a finite vertex type has a planar supergraph on that same type that is maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_augmentation_finite_maximal_extension {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by sorry
