-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_for_edge_upper_22808aa2
-- name    : WilliamsonShmoys.planar_triangulation_extension_for_edge_upper_22808aa2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:45:17.438674+00:00
-- url     : https://prove2.me/theorems/68e343da-c8bc-4a5b-8997-d165815a568e
-- title:
--   Same-vertex planar triangulation extension for the edge bound
-- statement:
--   Any finite simple graph with at least three vertices and the specified crossing-free drawing is contained in a graph on the same vertex type that has such a drawing and exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_for_edge_upper_22808aa2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ T : SimpleGraph V,
      K ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
