-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_repair_8fa97b2b
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_repair_8fa97b2b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:50:44.621387+00:00
-- url     : https://prove2.me/theorems/0f7d8c76-9243-4e78-b5c0-e2e6b23adc0c
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   A finite graph with a planar drawing is contained, on the same vertex type, in a graph with a planar drawing that is maximal under edge-set inclusion. Finiteness of V makes the collection of candidate edge sets finite; the original graph supplies a candidate, and planarity is preserved when deleting edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_repair_8fa97b2b
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ H.edgeSet := by sorry
