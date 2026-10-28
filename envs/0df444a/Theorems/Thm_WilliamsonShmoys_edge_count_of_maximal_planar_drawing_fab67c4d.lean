-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_fab67c4d
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing_fab67c4d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:30:15.334972+00:00
-- url     : https://prove2.me/theorems/2e1a0689-cd2d-4d58-840c-77e286835e74
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite ordered vertices, with no drawable strict edge supergraph on the same vertices, has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing_fab67c4d
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L.edgeSet ⊂ M.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn M) :
    (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
