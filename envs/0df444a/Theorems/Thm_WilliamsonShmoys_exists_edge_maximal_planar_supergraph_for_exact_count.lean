-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_for_exact_count
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_for_exact_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:44:04.86156+00:00
-- url     : https://prove2.me/theorems/eabccc53-f96c-40ea-9993-5739a0bc99d6
-- title:
--   Existence of an edge-maximal drawable supergraph for exact counting
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph maximal under edge inclusion. Maximize the number of edges among the finitely many drawable supergraphs; the family is nonempty because it contains `H`, and a drawable supergraph of a maximizer cannot have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_for_exact_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by sorry
