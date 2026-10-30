-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_fab67c4d
-- name    : WilliamsonShmoys.planar_drawing_edge_count_completion_fab67c4d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:27:13.950298+00:00
-- url     : https://prove2.me/theorems/fddd844c-a2be-46a1-8921-c16258f493bc
-- title:
--   Same-vertex planar edge-count completion
-- statement:
--   Every drawable finite simple graph with at least three vertices extends on the same vertex set to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_completion_fab67c4d
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeSet ⊆ M.edgeSet ∧
      3 * (Fintype.card V : Int) - 6 = (M.edgeSet.ncard : Int) := by sorry
