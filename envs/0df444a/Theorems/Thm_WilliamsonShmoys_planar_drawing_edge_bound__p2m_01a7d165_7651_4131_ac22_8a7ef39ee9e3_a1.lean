-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:57:36.601924+00:00
-- url     : https://prove2.me/theorems/cb41be71-821a-4ee1-8bbc-87748aa8233d
-- title:
--   Simple planar edge bound from a drawing
-- statement:
--   For a connected finite simple graph with at least three vertices and the supplied crossing-free drawing, prove the planar density bound `E + 6 ≤ 3V`. This removes the face-length/density estimate from the parent; together with the Euler equation, it implies that the total face-boundary length is at least three per face. A concrete route is to augment the embedded simple graph to a triangulation while preserving its vertices, then count each triangular face boundary three times and each edge at most twice, using Euler's formula. The lower bound of three vertices is needed for this form of the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_01a7d165_7651_4131_ac22_8a7ef39ee9e3_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hcard : 3 <= Fintype.card V) : K.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
