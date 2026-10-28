-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_fddd844c
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing_fddd844c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:33:16.398984+00:00
-- url     : https://prove2.me/theorems/c3ead240-fa43-405b-a40e-c25ede6c7235
-- title:
--   Edge count of an edge-maximal drawable simple graph
-- statement:
--   An edge-maximal drawable simple graph with at least three vertices has exactly 3|V|−6 edges. The intended proof derives connectivity and triangular faces from maximality, then uses Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing_fddd844c
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      M.edgeSet ⊆ N.edgeSet → N.edgeSet = M.edgeSet) :
    3 * (Fintype.card V : Int) - 6 = (M.edgeSet.ncard : Int) := by sorry
