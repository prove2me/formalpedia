-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:54:59.880701+00:00
-- url     : https://prove2.me/theorems/99cd9976-4307-421c-aac6-f259ef43e42f
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Any graph with the given crossing-free drawing and at least three vertices is contained in a graph on the same vertex type with a crossing-free drawing and exactly `3|V| - 6` edges. This packages the topological core: augment the drawing to a maximal planar graph, show its faces are triangular, and apply Euler’s formula. The vertex threshold is preserved because it is needed for the triangulation edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      N ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
