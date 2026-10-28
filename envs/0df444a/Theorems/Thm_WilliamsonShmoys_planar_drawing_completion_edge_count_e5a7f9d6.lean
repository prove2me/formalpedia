-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_count_e5a7f9d6
-- name    : WilliamsonShmoys.planar_drawing_completion_edge_count_e5a7f9d6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:09:55.274387+00:00
-- url     : https://prove2.me/theorems/22ddc852-2154-4a6c-ada4-27ad8bbf2673
-- title:
--   Complete a planar drawing to the triangulated edge count
-- statement:
--   Any graph with a crossing-free drawing on at least three vertices has a planar supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_completion_edge_count_e5a7f9d6
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧ K ≤ L ∧
        (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
