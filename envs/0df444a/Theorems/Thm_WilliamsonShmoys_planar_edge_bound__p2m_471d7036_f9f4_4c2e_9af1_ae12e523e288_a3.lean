-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a3
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:46:40.375578+00:00
-- url     : https://prove2.me/theorems/5d8e8105-9248-4e8a-84e6-9239becaa16b
-- title:
--   Simple planar graph edge bound
-- statement:
--   This child states the standard edge bound for a finite connected simple planar graph with at least three vertices. Its hypotheses retain the size boundary needed for the bound. A proof route is to define facial boundary walks for the drawing, count each edge twice across all face boundaries (including bridges twice), and show every facial boundary walk has length at least three for a simple connected graph with at least three vertices. Summing gives `3 * faceCount ≤ 2 * edgeCount`; combining with Euler’s formula yields the stated edge bound. The parent uses this child together with the existing published Euler face-count theorem. The topological construction and incidence counting remain the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
