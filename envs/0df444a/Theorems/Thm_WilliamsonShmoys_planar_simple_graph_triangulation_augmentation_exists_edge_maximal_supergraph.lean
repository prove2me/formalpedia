-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_triangulation_augmentation_exists_edge_maximal_supergraph
-- name    : WilliamsonShmoys.planar_simple_graph_triangulation_augmentation_exists_edge_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:38:21.577356+00:00
-- url     : https://prove2.me/theorems/72641cba-d8d0-47d5-bc31-b218bdb521b2
-- title:
--   Existence of a maximal drawable supergraph for triangulation augmentation
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices with no strictly larger drawable edge-set supergraph. The exact hypotheses preserve finiteness and the supplied vertex order required by HasPlanarDrawingOn; no lower bound on the vertex count is needed for this finite-maximization step. A proof can maximize edge-set cardinality over the finite family of drawable supergraphs containing H; any strict extension has larger cardinality and contradicts maximality. This removes the existence and maximality choice from the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_triangulation_augmentation_exists_edge_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
