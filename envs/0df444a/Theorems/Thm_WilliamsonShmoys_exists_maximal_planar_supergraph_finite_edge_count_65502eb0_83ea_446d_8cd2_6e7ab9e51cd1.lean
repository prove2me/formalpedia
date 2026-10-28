-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finite_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_finite_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:29:16.119555+00:00
-- url     : https://prove2.me/theorems/fac7e520-031e-4c7b-bff5-acfcf4409656
-- title:
--   Existence of a maximal planar supergraph by finite edge-count maximization
-- statement:
--   For every planar graph on a finite linearly ordered vertex type, there is a planar graph on the same vertices containing it whose edge set contains every planar supergraph edge set only when the two edge sets are equal. The candidate family is nonempty even for an empty vertex type because it contains the starting graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_finite_edge_count_65502eb0_83ea_446d_8cd2_6e7ab9e51cd1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet ⊆ H.edgeSet ∧
      (∀ J : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn J →
        H.edgeSet ⊆ J.edgeSet → J.edgeSet ⊆ H.edgeSet) := by sorry
