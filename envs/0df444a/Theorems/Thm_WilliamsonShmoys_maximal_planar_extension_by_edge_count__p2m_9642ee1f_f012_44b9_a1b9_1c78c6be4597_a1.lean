-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_by_edge_count__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_by_edge_count__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:00.035877+00:00
-- url     : https://prove2.me/theorems/f330d4c2-9c1a-4a03-91e8-570c68857cc4
-- title:
--   Maximum edge count among drawable extensions
-- statement:
--   Among drawable supergraphs of the given drawable graph, there is one whose edge count is at least the starting graph’s and at least that of every drawable supergraph of the chosen graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_by_edge_count__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (letI : DecidableRel G.Adj := Classical.decRel G.Adj; letI : DecidableRel H.Adj := Classical.decRel H.Adj; G.edgeFinset.card ≤ H.edgeFinset.card) ∧ (∀ K : SimpleGraph V, (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn K → (letI : DecidableRel H.Adj := Classical.decRel H.Adj; letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card ≤ H.edgeFinset.card)) := by sorry
