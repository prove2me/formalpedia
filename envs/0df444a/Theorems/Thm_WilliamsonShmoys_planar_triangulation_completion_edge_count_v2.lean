-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count_v2
-- name    : WilliamsonShmoys.planar_triangulation_completion_edge_count_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:02:32.115271+00:00
-- url     : https://prove2.me/theorems/a6cc6ce2-4479-4e22-ad6e-c928f195198d
-- title:
--   Drawable graphs extend to a drawable graph with the triangulation edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph with exactly 3n − 6 edges. This removes the planar completion and edge-counting work from the parent. An independent proof route extends the drawing to a maximal planar embedding, proves each face is triangular, then applies Euler’s formula and counts face-edge incidences. At n = 3 the completion is the triangle; the remaining core is formalizing completion and face counting for the explicit arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_edge_count_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
