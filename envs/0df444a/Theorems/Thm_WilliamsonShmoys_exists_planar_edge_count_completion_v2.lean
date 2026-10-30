-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_completion_v2
-- name    : WilliamsonShmoys.exists_planar_edge_count_completion_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:04:03.584617+00:00
-- url     : https://prove2.me/theorems/a3317d7a-4b18-491b-9aee-6f2b4185d855
-- title:
--   Complete a finite planar drawing to the triangulation edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained in a drawable graph on the same vertex set with the triangulation edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_edge_count_completion_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hV : 3 ≤ Fintype.card V) :
    ∃ Z : SimpleGraph V,
      LE.le Y Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      Z.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
