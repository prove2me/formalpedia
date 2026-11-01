-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_extension_by_edge_count__p2m_f330d4c2_9c1a_4a03_91e8_570c68857cc4_a1
-- name    : WilliamsonShmoys.exists_maximal_simpleGraph_extension_by_edge_count__p2m_f330d4c2_9c1a_4a03_91e8_570c68857cc4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:16:43.129554+00:00
-- url     : https://prove2.me/theorems/ca6aefdd-464a-410c-87c0-eff497895a05
-- title:
--   Finite maximal extension by edge count
-- statement:
--   For any property of graphs on a finite ordered vertex type, if `G` has the property, there is a supergraph `H` with the property and at least as many edges as `G`, such that every supergraph of `H` with the property has no more edges than `H`. This isolates the finite maximization argument used by the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_simpleGraph_extension_by_edge_count__p2m_f330d4c2_9c1a_4a03_91e8_570c68857cc4_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) : ∃ H : SimpleGraph V, (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧ P H ∧ (letI : DecidableRel G.Adj := Classical.decRel G.Adj; letI : DecidableRel H.Adj := Classical.decRel H.Adj; G.edgeFinset.card ≤ H.edgeFinset.card) ∧ (∀ K : SimpleGraph V, (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) → P K → (letI : DecidableRel H.Adj := Classical.decRel H.Adj; letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card ≤ H.edgeFinset.card)) := by sorry
