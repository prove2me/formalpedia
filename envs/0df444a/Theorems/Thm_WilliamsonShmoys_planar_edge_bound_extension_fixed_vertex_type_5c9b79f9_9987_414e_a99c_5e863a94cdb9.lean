-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_extension_fixed_vertex_type_5c9b79f9_9987_414e_a99c_5e863a94cdb9
-- name    : WilliamsonShmoys.planar_edge_bound_extension_fixed_vertex_type_5c9b79f9_9987_414e_a99c_5e863a94cdb9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:58:48.190228+00:00
-- url     : https://prove2.me/theorems/4d4521ad-8ce4-4c29-bfad-617e82943bc3
-- title:
--   Planar extension with the fixed vertex type edge bound
-- statement:
--   Every graph with the supplied planar drawing on a finite linearly ordered vertex type of size at least three has a planar supergraph on that same vertex type with at least 3|V| − 6 edges. The parent combines this extension with maximality to identify the supergraph with K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_extension_fixed_vertex_type_5c9b79f9_9987_414e_a99c_5e863a94cdb9
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V =>
      And (K <= H) (And (WilliamsonShmoys.HasPlanarDrawingOn H)
        (3 * Fintype.card V - 6 <= H.edgeSet.ncard)) := by sorry
