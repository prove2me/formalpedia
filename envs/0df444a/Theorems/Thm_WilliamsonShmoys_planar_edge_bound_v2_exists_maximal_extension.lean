-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_v2_exists_maximal_extension
-- name    : WilliamsonShmoys.planar_edge_bound_v2_exists_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:57:18.745277+00:00
-- url     : https://prove2.me/theorems/0ac8b2ef-1eac-486b-ba01-ddc54886e198
-- title:
--   Maximal planar extension on a fixed vertex set
-- statement:
--   Every graph with the supplied planar drawing has an inclusion-maximal planar supergraph on the same finite vertex type, and the extension contains at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_v2_exists_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ K : SimpleGraph V, Q ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) ∧
      Q.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
