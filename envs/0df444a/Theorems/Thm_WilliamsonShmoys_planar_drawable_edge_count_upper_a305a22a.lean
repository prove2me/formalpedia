-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_count_upper_a305a22a
-- name    : WilliamsonShmoys.planar_drawable_edge_count_upper_a305a22a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:40:11.054525+00:00
-- url     : https://prove2.me/theorems/70737efd-41f9-48b6-8858-dc226f716467
-- title:
--   Upper edge bound for a drawable graph
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| - 6 edges. This removes the Euler and face-incidence counting obligation from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_edge_count_upper_a305a22a
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
