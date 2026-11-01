-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_bound__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
-- name    : WilliamsonShmoys.planarDrawing_edge_bound__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:27:01.230922+00:00
-- url     : https://prove2.me/theorems/af29040b-5f5f-41c7-ae26-98a3e427e1bc
-- title:
--   Simple planar graph edge bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges, expressed without natural subtraction as m + 6 ≤ 3n. The size hypothesis is necessary for this bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_edge_bound__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by sorry
