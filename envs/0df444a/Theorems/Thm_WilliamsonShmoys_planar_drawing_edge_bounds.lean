-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bounds
-- name    : WilliamsonShmoys.planar_drawing_edge_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:34:56.9251+00:00
-- url     : https://prove2.me/theorems/5cdd1ade-55f2-40c6-a383-815a2e0ef521
-- title:
--   Edge bounds for a connected graph with a planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and the supplied crossing-free drawing has at least |V| − 1 edges and at most 3|V| − 6 edges. Connectedness gives the lower bound. The upper bound follows from the planar edge bound for a simple graph embedded in the plane.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    Fintype.card V <= K.edgeSet.ncard + 1 ∧
      K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
