-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_extension
-- name    : WilliamsonShmoys.planar_drawing_edge_count_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:07:58.437301+00:00
-- url     : https://prove2.me/theorems/784d1fda-4529-43fd-94a5-bf399d6fa183
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Every graph with the specified planar drawing, at least three vertices, and fewer than 3|V|−6 edges has a strictly larger planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 ≤ Fintype.card V)
    (hE : P.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ Q : SimpleGraph V,
      P.edgeSet ⊂ Q.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q := by sorry
