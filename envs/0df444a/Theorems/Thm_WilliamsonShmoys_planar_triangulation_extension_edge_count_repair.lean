-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count_repair
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count_repair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:29:43.821225+00:00
-- url     : https://prove2.me/theorems/95c30299-2304-41f3-9bac-8dc8e110021d
-- title:
--   Planar augmentation with exact edge count
-- statement:
--   Any finite graph with at least three vertices and a crossing-free drawing is contained, on the same vertices, in a drawable graph with exactly three times the number of vertices minus six edges. The parent uses maximality to identify this extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
