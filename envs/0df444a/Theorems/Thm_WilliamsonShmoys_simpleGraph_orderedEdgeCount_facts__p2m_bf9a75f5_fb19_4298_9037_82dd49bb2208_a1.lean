-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_orderedEdgeCount_facts__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1
-- name    : WilliamsonShmoys.simpleGraph_orderedEdgeCount_facts__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:13:16.990578+00:00
-- url     : https://prove2.me/theorems/0c6db297-72bf-4106-a445-c2372bf77dfb
-- title:
--   Bounds and strict monotonicity of ordered adjacency-pair count
-- statement:
--   For every finite simple graph, the number of ordered adjacent vertex pairs is at most the size of V × V, and that number strictly increases under strict graph inclusion. The explicit decidability binders make the subtype cardinalities well-formed; the parent can provide them classically. The bound uses the subtype inclusion into V × V. Strict inclusion gives an adjacent pair in the larger graph absent from the smaller, making the induced finite subtype inclusion proper and its cardinality strictly larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_orderedEdgeCount_facts__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1 {V : Type} [Fintype V] (H H' : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel H'.Adj] : (∀ (K : SimpleGraph V) [DecidableRel K.Adj], Fintype.card {p : V × V // K.Adj p.1 p.2} ≤ Fintype.card (V × V)) ∧ (H < H' → Fintype.card {p : V × V // H.Adj p.1 p.2} < Fintype.card {p : V × V // H'.Adj p.1 p.2}) := by sorry
