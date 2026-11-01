-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:59:56.763917+00:00
-- url     : https://prove2.me/theorems/2fe19a03-1e65-4d28-a5ac-44bfa44bd1e6
-- title:
--   Monotonicity of edge-set cardinality under adjacency inclusion
-- statement:
--   For finite graphs on the same vertex type, adjacency inclusion induces inclusion of edge sets and hence monotonicity of their cardinalities. Prove by showing `G.edgeSet ⊆ H.edgeSet` and using finite-set cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V)
    (hsub : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
