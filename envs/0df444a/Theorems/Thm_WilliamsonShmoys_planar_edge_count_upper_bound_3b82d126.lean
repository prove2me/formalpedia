-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_3b82d126
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_3b82d126
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:32:33.106991+00:00
-- url     : https://prove2.me/theorems/f7f0ac3c-524d-4a73-b598-c94734690a27
-- title:
--   Edge-count upper bound for a planar drawing
-- statement:
--   A graph with the supplied crossing-free drawing and at least three vertices has at most \(3|V|-6\) edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_3b82d126
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
