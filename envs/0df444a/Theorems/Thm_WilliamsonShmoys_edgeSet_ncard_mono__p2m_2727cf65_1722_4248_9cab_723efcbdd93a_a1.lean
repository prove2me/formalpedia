-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:49.959214+00:00
-- url     : https://prove2.me/theorems/496923ea-1868-4170-8814-27fb8ae42ea2
-- title:
--   Monotonicity of edge count under graph inclusion
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its edge count is no larger. This follows by edge-set inclusion and monotonicity of finite cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_2727cf65_1722_4248_9cab_723efcbdd93a_a1 {V : Type} [Fintype V] (G H : SimpleGraph V) (hGH : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
