-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximizing_edges
-- name    : WilliamsonShmoys.exists_planar_supergraph_maximizing_edges
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:37:50.576791+00:00
-- url     : https://prove2.me/theorems/97518344-5f8d-41f0-81af-be8f3e20df6e
-- title:
--   A planar supergraph maximizing edge count exists
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertex set whose edge count is at least that of every other planar supergraph on that vertex set. This is obtained by maximizing edge count over the finite family of simple graphs on the vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_maximizing_edges
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet.ncard ≤ M.edgeSet.ncard := by
  sorry
