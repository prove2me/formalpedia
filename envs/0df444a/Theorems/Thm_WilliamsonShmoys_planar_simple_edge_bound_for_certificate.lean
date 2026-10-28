-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_for_certificate
-- name    : WilliamsonShmoys.planar_simple_edge_bound_for_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:37:14.228672+00:00
-- url     : https://prove2.me/theorems/38ffb807-3383-4fe4-bc93-a2933793897a
-- title:
--   Simple planar graph edge bound
-- statement:
--   A simple graph with at least three vertices and the supplied crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_bound_for_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
