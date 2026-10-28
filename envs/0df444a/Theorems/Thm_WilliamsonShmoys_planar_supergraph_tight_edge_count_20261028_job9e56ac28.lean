-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_tight_edge_count_20261028_job9e56ac28
-- name    : WilliamsonShmoys.planar_supergraph_tight_edge_count_20261028_job9e56ac28
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:15:43.275205+00:00
-- url     : https://prove2.me/theorems/f91a7477-6c0a-4afa-b69f-27a2957148ef
-- title:
--   Planar drawings extend to a supergraph with the triangulation edge count
-- statement:
--   If a graph on at least three vertices has a drawing satisfying the supplied crossing-free arc predicate, then it has a drawable supergraph on the same vertices with exactly 3n − 6 edges. This extension result does not assume maximality of the original graph, so the parent applies maximality to show its extension has the same edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_tight_edge_count_20261028_job9e56ac28
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
