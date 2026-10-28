-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound
-- name    : WilliamsonShmoys.simple_planar_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:25:48.555226+00:00
-- url     : https://prove2.me/theorems/65ae16f5-20a3-4f86-803d-8e9e2da9b48d
-- title:
--   Edge bound for a simple planar graph
-- statement:
--   A connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most 3V−6 edges. This is the standard simple-planar edge bound; it captures the main remaining planar counting obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.simple_planar_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
