-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:32:49.99298+00:00
-- url     : https://prove2.me/theorems/a212ef03-91b2-4849-b5f4-521b2c843c8b
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A drawable simple graph with at least three vertices has at most 3|V|−6 edges, expressed as 3|V| ≤ |E|+6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
