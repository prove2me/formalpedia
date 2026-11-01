-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_to_edge_bound__p2m_707bc162_d7c2_4f63_9fb7_a67d4965e3da_a1
-- name    : WilliamsonShmoys.planar_augmentation_to_edge_bound__p2m_707bc162_d7c2_4f63_9fb7_a67d4965e3da_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:01.775305+00:00
-- url     : https://prove2.me/theorems/f6ec1c8b-29dd-423f-98a5-ccb065f177a1
-- title:
--   Augment a planar drawing to the planar edge bound
-- statement:
--   For at least three vertices, augment a drawable graph on the same vertices to a drawable graph attaining the planar simple-graph edge bound, while retaining every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_to_edge_bound__p2m_707bc162_d7c2_4f63_9fb7_a67d4965e3da_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (dG : DecidableRel G.Adj) (hG : HasPlanarDrawingOn G) (hn : 3 ≤ Fintype.card V) : ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj), HasPlanarDrawingOn Q ∧ (letI : DecidableRel G.Adj := dG; letI : DecidableRel Q.Adj := dQ; G.edgeFinset ⊆ Q.edgeFinset) ∧ (letI : DecidableRel Q.Adj := dQ; Q.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
