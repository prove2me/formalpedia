-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_exists_maximal_extension
-- name    : WilliamsonShmoys.planar_simple_edge_bound_exists_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:31:12.675071+00:00
-- url     : https://prove2.me/theorems/12f0d1f9-ef4f-48b6-9982-02de6345868f
-- title:
--   Maximal planar extension for the edge bound
-- statement:
--   Extend a graph with a crossing-free drawing to an inclusion-maximal planar supergraph on the same finite vertex type, retaining all original edges and at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_bound_exists_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ u v, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
