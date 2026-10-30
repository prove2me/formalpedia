-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augment_to_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_augment_to_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:18:43.968983+00:00
-- url     : https://prove2.me/theorems/e75b6e91-534a-413b-8fc4-4bbb1863da27
-- title:
--   Complete a planar drawing to the Euler edge bound
-- statement:
--   Every drawable simple graph on a finite ordered vertex type of size at least three extends on the same vertices to a drawable graph with exactly `3|V|−6` edges. The boundary case of three vertices is the triangle. The proof route is to add edges through faces until the plane embedding is maximal and then apply Euler's formula; this supplies the geometric completion work needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_augment_to_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
