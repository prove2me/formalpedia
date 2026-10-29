-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_exists
-- name    : WilliamsonShmoys.planar_drawing_triangulation_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:43:12.910084+00:00
-- url     : https://prove2.me/theorems/9e21c741-b5c0-4933-97e7-5289265ae8e7
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Every drawable simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
