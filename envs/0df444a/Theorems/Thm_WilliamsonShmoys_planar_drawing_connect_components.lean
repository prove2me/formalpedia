-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connect_components
-- name    : WilliamsonShmoys.planar_drawing_connect_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:01:19.572229+00:00
-- url     : https://prove2.me/theorems/82c4f8ed-ece1-465d-8ede-f03c4753c646
-- title:
--   Connect the components of a planar drawing without losing edges
-- statement:
--   For a disconnected graph on at least three vertices with the specified crossing-free drawing, there is a connected planar supergraph on the same vertex type whose edge count is at least the original’s. A proof route is to use the finite disjoint drawing components and route connecting arcs through the complement, verifying the arc endpoint, vertex-avoidance, and nonintersection conditions in HasPlanarDrawingOn. This geometric routing is the main unresolved work in the reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connect_components
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.Connected := by sorry
