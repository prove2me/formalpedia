-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_components_connectible__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
-- name    : WilliamsonShmoys.planar_drawing_components_connectible__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:24.792201+00:00
-- url     : https://prove2.me/theorems/984d7be3-d630-4a9d-be8d-9ea0b89ae665
-- title:
--   Connect components of a planar drawing
-- statement:
--   Extend the given drawn graph to a connected drawn graph on the same finite vertex type, retaining every original edge. The vertex-count hypothesis is preserved. This removes disconnected-graph bookkeeping from the parent. A proof route is to derive a plane embedding from the drawing and join components through suitable faces while avoiding the existing drawing. The existence of such an extension and the topological construction are the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_components_connectible__p2m_ba06bb4d_e92b_4537_887e_0721c652813c_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard <= K.edgeSet.ncard := by sorry
