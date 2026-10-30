-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_fixed_vertex_planar_edge_lower_bound
-- name    : WilliamsonShmoys.maximal_fixed_vertex_planar_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:39:15.178572+00:00
-- url     : https://prove2.me/theorems/5c9b79f9-9987-414e-a99c-5e863a94cdb9
-- title:
--   Edge lower bound for a maximal planar graph on a fixed vertex type
-- statement:
--   A planar graph on at least three vertices that has no strict planar supergraph on the same vertex type has at least `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_fixed_vertex_planar_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall H : SimpleGraph V,
      K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by sorry
