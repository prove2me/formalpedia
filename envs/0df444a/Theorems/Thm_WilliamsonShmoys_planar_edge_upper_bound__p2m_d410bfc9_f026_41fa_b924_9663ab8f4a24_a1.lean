-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:09:55.387621+00:00
-- url     : https://prove2.me/theorems/e48a9b75-900b-4b45-ae03-6bdcae2a59f8
-- title:
--   Euler upper bound for a drawable simple graph
-- statement:
--   For a finite drawable simple graph with at least three vertices, its edge count is at most 3|V|−6. This is the Euler upper-bound half of the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_d410bfc9_f026_41fa_b924_9663ab8f4a24_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
