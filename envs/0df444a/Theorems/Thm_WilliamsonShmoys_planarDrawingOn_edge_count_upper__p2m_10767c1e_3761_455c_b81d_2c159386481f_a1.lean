-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edge_count_upper__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1
-- name    : WilliamsonShmoys.planarDrawingOn_edge_count_upper__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:00:26.720088+00:00
-- url     : https://prove2.me/theorems/f2f8478a-ac3d-4094-98b9-a21bbb0fec9b
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   Every graph with a drawing as defined by `HasPlanarDrawingOn`, on at least three finite vertices, has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_edge_count_upper__p2m_10767c1e_3761_455c_b81d_2c159386481f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
