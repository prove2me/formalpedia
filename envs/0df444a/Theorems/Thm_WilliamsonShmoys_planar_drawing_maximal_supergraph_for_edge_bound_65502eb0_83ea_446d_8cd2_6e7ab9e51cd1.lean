-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_for_edge_bound_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_for_edge_bound_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:00:28.503393+00:00
-- url     : https://prove2.me/theorems/d45bcc96-ddcf-4c50-adca-5b8e7344ad50
-- title:
--   Maximal planar supergraph on the same vertices
-- statement:
--   Any graph with the given planar drawing is contained in an edge-maximal graph with a planar drawing on the same vertex type, and its edge count is no larger. A finite maximization over simple graphs on V gives a proof route: choose a planar supergraph with maximum edge count, then use finiteness and edge inclusion to show that any planar graph containing it has the same edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_for_edge_bound_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet ⊆ H.edgeSet ∧
      (∀ J : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn J →
        H.edgeSet ⊆ J.edgeSet → J.edgeSet ⊆ H.edgeSet) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
