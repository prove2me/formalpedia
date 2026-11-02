-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count__p2m_2caeaad5_0df9_4946_9307_3d000f81b17e_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_count__p2m_2caeaad5_0df9_4946_9307_3d000f81b17e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:00:39.404192+00:00
-- url     : https://prove2.me/theorems/12f5c168-d721-449d-bfa4-74e61d52c450
-- title:
--   Planar supergraph edge lower bound
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex type whose edge count is at least three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_count__p2m_2caeaad5_0df9_4946_9307_3d000f81b17e_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : ∃ S : SimpleGraph V, G ≤ S ∧ HasPlanarDrawingOn S ∧ ∀ [DecidableRel S.Adj], 3 * Fintype.card V - 6 ≤ S.edgeFinset.card := by sorry
