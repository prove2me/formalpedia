-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:37:21.840981+00:00
-- url     : https://prove2.me/theorems/aac86d47-8693-45f7-b804-15c4676bd904
-- title:
--   Planar simple graph edge bound
-- statement:
--   A drawable simple graph with at least three vertices has at most 3|V|−6 edges, expressed as |E|+6 ≤ 3|V|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
