-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_bound__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_edge_bound__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:22.796596+00:00
-- url     : https://prove2.me/theorems/81ed959b-71ee-4030-85d8-875841fa0344
-- title:
--   Simple edge bound for a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges, counted with `Set.ncard` to avoid requiring a decidable adjacency instance. A proof route augments the drawing to a triangulation, applies Euler’s formula, and uses the lower bound of three on face boundary lengths. This supplies the connected case used by the parent; formalizing augmentation and the face-count argument remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_edge_bound__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
