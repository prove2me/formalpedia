-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count_fixed_vertices
-- name    : WilliamsonShmoys.planar_augmentation_edge_count_fixed_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:35:06.836396+00:00
-- url     : https://prove2.me/theorems/d59862b3-4e99-4fc0-bdea-a0a653d282d8
-- title:
--   Planar augmentation with a fixed vertex set
-- statement:
--   Every drawable simple graph on at least three vertices is contained in a drawable graph on the same vertex set with exactly 3n−6 edges. This is the planar augmentation and Euler-counting step; at n=3 it yields the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_augmentation_edge_count_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
