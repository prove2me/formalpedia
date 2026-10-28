-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_by_edge_inclusion
-- name    : WilliamsonShmoys.planar_supergraph_maximal_by_edge_inclusion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:00:05.243029+00:00
-- url     : https://prove2.me/theorems/1ae15a99-ac42-401c-aee1-35712f066f46
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type has a planar supergraph on that same vertex type which is maximal under edge inclusion among planar graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_by_edge_inclusion
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      J.edgeSet ⊆ K.edgeSet ∧
      ∀ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeSet ⊆ L.edgeSet →
        L.edgeSet ⊆ K.edgeSet := by sorry
