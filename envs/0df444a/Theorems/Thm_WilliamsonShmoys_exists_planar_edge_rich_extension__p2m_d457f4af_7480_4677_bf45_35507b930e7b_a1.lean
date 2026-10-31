-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_rich_extension__p2m_d457f4af_7480_4677_bf45_35507b930e7b_a1
-- name    : WilliamsonShmoys.exists_planar_edge_rich_extension__p2m_d457f4af_7480_4677_bf45_35507b930e7b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:51:26.912832+00:00
-- url     : https://prove2.me/theorems/2cac5e96-6851-49ac-b8de-d75bb175e3cb
-- title:
--   Planar drawing admits an edge-rich extension
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with at least `3n - 6` edges. The child isolates the triangulation/Euler argument; the parent applies maximality to identify the extension’s edge set with the original one.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_planar_edge_rich_extension__p2m_d457f4af_7480_4677_bf45_35507b930e7b_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ 3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
