-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_euler_upper_bound_v2
-- name    : WilliamsonShmoys.planar_edge_count_euler_upper_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:36:03.912932+00:00
-- url     : https://prove2.me/theorems/3ead9850-1490-43ae-8f54-bebdce4f175a
-- title:
--   Euler upper bound for edges in a finite planar graph
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_euler_upper_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
