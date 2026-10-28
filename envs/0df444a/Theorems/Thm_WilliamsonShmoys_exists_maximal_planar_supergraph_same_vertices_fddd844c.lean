-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices_fddd844c
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices_fddd844c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:25:56.47051+00:00
-- url     : https://prove2.me/theorems/57395774-283e-4364-acd9-f369cb0eea5c
-- title:
--   Existence of an edge-maximal drawable supergraph on the same vertices
-- statement:
--   A drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal under edge inclusion among drawable graphs. The size hypothesis is retained to match the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices_fddd844c
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeSet ⊆ M.edgeSet ∧
      ∀ N : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn N →
        M.edgeSet ⊆ N.edgeSet →
        N.edgeSet = M.edgeSet := by sorry
