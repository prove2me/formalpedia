-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_for_triangular_incidence_count
-- name    : WilliamsonShmoys.planar_edge_upper_for_triangular_incidence_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:10:34.82601+00:00
-- url     : https://prove2.me/theorems/447d55a9-2bd3-4bee-aeac-b9e7c1d6e8dd
-- title:
--   Planar drawing edge upper bound for incidence count
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The drawing and size hypotheses are preserved, including the boundary case of exactly three vertices. This removes the general planar edge upper-bound argument from the parent. A proof route is to establish Euler's formula for the drawing, account for face-edge incidences, and handle disconnected drawings before deriving the bound. The core obligation is formalizing that planar counting argument for the supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_for_triangular_incidence_count
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hCard : 3 <= Fintype.card V) :
    (X.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by sorry
