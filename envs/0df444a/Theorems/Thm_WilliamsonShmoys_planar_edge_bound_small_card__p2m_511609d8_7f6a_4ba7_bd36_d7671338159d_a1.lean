-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_small_card__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
-- name    : WilliamsonShmoys.planar_edge_bound_small_card__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:07.883386+00:00
-- url     : https://prove2.me/theorems/283a5f49-22ce-49fe-9661-5c967127d016
-- title:
--   Simple-graph edge bound below three vertices
-- statement:
--   For a finite simple graph on fewer than three vertices, its edge count is at most the number of unordered pairs of vertices. The cases of 0, 1, and 2 vertices give bounds 0, 0, and 1, respectively.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_small_card__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hsmall : Fintype.card V < 3) :
    L.edgeFinset.card ≤ (Fintype.card V).choose 2 := by sorry
