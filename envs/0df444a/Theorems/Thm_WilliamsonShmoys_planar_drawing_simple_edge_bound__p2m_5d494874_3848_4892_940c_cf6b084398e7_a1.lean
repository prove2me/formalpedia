-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
-- name    : WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:14.032773+00:00
-- url     : https://prove2.me/theorems/4939bc54-bf93-4b2e-bbee-bc8378b5882a
-- title:
--   Simple planar graph edge bound
-- statement:
--   A simple graph on at least three vertices with a drawing satisfying `HasPlanarDrawingOn` has at most `3V − 6` edges, whether or not it is connected. This supplies the quantitative planar bound needed with Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_5d494874_3848_4892_940c_cf6b084398e7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
