-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_on_finite_ordered_type
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_on_finite_ordered_type
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:35:54.365957+00:00
-- url     : https://prove2.me/theorems/56bdad8b-5ae1-4e55-8b12-01d5eae92488
-- title:
--   A finite ordered planar graph has an edge-maximal planar supergraph
-- statement:
--   On the fixed finite ordered vertex type, a graph with a planar drawing has a planar supergraph that admits no strictly larger planar edge supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_on_finite_ordered_type
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet := by
  sorry
