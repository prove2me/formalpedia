-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_7c5eea9e
-- name    : WilliamsonShmoys.simple_planar_edge_bound_7c5eea9e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:51:22.350729+00:00
-- url     : https://prove2.me/theorems/7121c0f2-4dee-42e3-b079-642bc756d54a
-- title:
--   Edge bound for a simple planar graph
-- statement:
--   A finite simple graph with at least three vertices and the supplied crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simple_planar_edge_bound_7c5eea9e
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
