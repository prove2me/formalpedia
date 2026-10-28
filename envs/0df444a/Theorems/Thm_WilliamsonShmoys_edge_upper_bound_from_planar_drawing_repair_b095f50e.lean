-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_upper_bound_from_planar_drawing_repair_b095f50e
-- name    : WilliamsonShmoys.edge_upper_bound_from_planar_drawing_repair_b095f50e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:18:20.629914+00:00
-- url     : https://prove2.me/theorems/a5958c18-8c90-4cab-aba7-b1c2588f0bad
-- title:
--   Planar edge upper bound from a drawing
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V| − 6 edges. This supplies the target's upper inequality. A proof can use Euler's formula and face-edge incidence counting, with separate treatment of small components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_upper_bound_from_planar_drawing_repair_b095f50e
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    W.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
