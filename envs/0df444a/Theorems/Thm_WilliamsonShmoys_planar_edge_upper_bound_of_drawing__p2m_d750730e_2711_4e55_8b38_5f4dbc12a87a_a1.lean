-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_of_drawing__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound_of_drawing__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:59:32.723109+00:00
-- url     : https://prove2.me/theorems/c643eab9-16cc-4e69-8d73-dd1e68fa5bd2
-- title:
--   Edge bound for a finite drawable graph
-- statement:
--   A drawable simple graph on at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_of_drawing__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel W.Adj := Classical.decRel W.Adj
    W.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
