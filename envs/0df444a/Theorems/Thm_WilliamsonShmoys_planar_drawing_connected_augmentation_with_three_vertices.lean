-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_with_three_vertices
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_with_three_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:00:58.531984+00:00
-- url     : https://prove2.me/theorems/b341ee93-3072-4db1-9c71-290e04bcaf83
-- title:
--   Connect a planar graph on at least three vertices
-- statement:
--   Extend a graph with a crossing-free drawing to a connected graph on the same vertex set, preserving a crossing-free drawing and not decreasing the edge count; the vertex set has at least three elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_with_three_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
