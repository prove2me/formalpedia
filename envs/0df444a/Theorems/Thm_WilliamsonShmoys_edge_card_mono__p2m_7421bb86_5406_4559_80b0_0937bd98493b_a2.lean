-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_mono__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
-- name    : WilliamsonShmoys.edge_card_mono__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:43:38.646232+00:00
-- url     : https://prove2.me/theorems/53f0cbc4-8646-45a3-af00-ff9c06f7e625
-- title:
--   Monotonicity of edge count under graph inclusion
-- statement:
--   If G is a subgraph of K on the same finite vertex type, its edge count is no larger. The proof route uses inclusion of the corresponding edge finsets and cardinality monotonicity. The statement retains the classical adjacency decision instances required by edgeFinset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_card_mono__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2 {V : Type} [Fintype V] (G K : SimpleGraph V) (hGK : G ≤ K) : (letI : DecidableRel G.Adj := Classical.decRel G.Adj; letI : DecidableRel K.Adj := Classical.decRel K.Adj; G.edgeFinset.card ≤ K.edgeFinset.card) := by sorry
