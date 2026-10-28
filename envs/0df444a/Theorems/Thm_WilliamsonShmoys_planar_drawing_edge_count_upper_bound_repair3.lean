-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_repair3
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_repair3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:47:11.205984+00:00
-- url     : https://prove2.me/theorems/0d418da7-c67d-4d6d-b9d9-ad983fde32a1
-- title:
--   Planar edge-count upper bound
-- statement:
--   Any finite simple graph with a drawing satisfying `HasPlanarDrawingOn` and at least three vertices has at most `3|V| − 6` edges. This removes the universal upper-bound obligation from the parent; a proof route is Euler’s formula with face-degree counting, including the disconnected case by connecting components. The `|V| ≥ 3` condition is retained for the standard bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
