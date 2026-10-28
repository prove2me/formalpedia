-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_fddd844c
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fddd844c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:59:08.541855+00:00
-- url     : https://prove2.me/theorems/1c3af418-60f6-43cb-bce2-5b8b37d68734
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   An edge-maximal graph with the supplied drawing and at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fddd844c
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      M.edgeSet ⊆ N.edgeSet → N.edgeSet = M.edgeSet) :
    3 * (Fintype.card V : Int) - 6 ≤ (M.edgeSet.ncard : Int) := by sorry
