-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_same_vertex_set_d3f6855c
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_same_vertex_set_d3f6855c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:46:03.929966+00:00
-- url     : https://prove2.me/theorems/957bde25-6adc-4708-a09b-ebc3230d75e7
-- title:
--   Extend a planar drawing to a same-vertex-set triangulation
-- statement:
--   Any finite simple graph with a crossing-free drawing on at least three vertices has a crossing-free supergraph on the same vertex set with exactly `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_same_vertex_set_d3f6855c
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L /\
      L.edgeSet.ncard = 3 * Fintype.card V - 6 /\
      WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
