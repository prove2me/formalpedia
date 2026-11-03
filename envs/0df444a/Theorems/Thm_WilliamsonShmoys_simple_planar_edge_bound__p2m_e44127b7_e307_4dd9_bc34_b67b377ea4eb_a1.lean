-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_e44127b7_e307_4dd9_bc34_b67b377ea4eb_a1
-- name    : WilliamsonShmoys.simple_planar_edge_bound__p2m_e44127b7_e307_4dd9_bc34_b67b377ea4eb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:11:29.896747+00:00
-- url     : https://prove2.me/theorems/32bf577a-e5b9-4d87-aee2-e2a1e821aee9
-- title:
--   Simple planar graph edge bound
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing on the plane has at most 3|V| − 6 edges. The proof route extracts face-boundary walks from the drawing, counts each edge twice across all face boundaries, uses that each face boundary has length at least three, and applies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.simple_planar_edge_bound__p2m_e44127b7_e307_4dd9_bc34_b67b377ea4eb_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hcard : 3 <= Fintype.card V) : K.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
