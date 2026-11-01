-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:21.090965+00:00
-- url     : https://prove2.me/theorems/b7056521-a4a1-40e5-a0cb-f48952c4d7e1
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Extend a finite simple graph with at least three vertices and a crossing-free drawing to a connected planar graph on the same vertices, preserving all original edges. The edge-count comparison uses `K.edgeSet.ncard` so the statement does not require a decidable adjacency instance for the existential graph. A proof route connects the finitely many drawn components through faces of the drawing. This removes disconnectedness from the parent argument; constructing the connecting arcs while preserving the drawing conditions is the remaining obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_4939bc54_bf93_4b2e_bbee_bc8378b5882a_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K ∧
        H.edgeFinset.card ≤ K.edgeSet.ncard := by sorry
