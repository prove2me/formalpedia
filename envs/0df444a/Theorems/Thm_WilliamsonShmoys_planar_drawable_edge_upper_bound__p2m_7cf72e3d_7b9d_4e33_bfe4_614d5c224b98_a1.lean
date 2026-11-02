-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_upper_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
-- name    : WilliamsonShmoys.planar_drawable_edge_upper_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:41:37.252559+00:00
-- url     : https://prove2.me/theorems/2115473c-36f0-41ff-984e-eaea18127678
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Any finite simple graph on at least three vertices with a crossing-free drawing as defined by HasPlanarDrawingOn has at most 3n−6 edges. The order and decidable adjacency arguments are retained to match the target’s representation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_edge_upper_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (dM : DecidableRel M.Adj) (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) : M.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
