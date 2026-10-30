-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_6274f47d
-- name    : WilliamsonShmoys.maximal_planar_edge_count_6274f47d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:08:48.298629+00:00
-- url     : https://prove2.me/theorems/fb05ef93-056c-4c21-9ad8-ef99e95b626a
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices with no proper drawable supergraph on the same vertex type has exactly `3|V| − 6` edges. A proof route establishes connectivity and triangular faces from maximality, handles the three-vertex case, and applies Euler’s formula and face-edge counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_6274f47d
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet = M.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
