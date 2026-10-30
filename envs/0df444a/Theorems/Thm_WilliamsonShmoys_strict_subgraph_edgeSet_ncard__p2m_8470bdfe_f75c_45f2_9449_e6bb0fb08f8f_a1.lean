-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_subgraph_edgeSet_ncard__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
-- name    : WilliamsonShmoys.strict_subgraph_edgeSet_ncard__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:07.603696+00:00
-- url     : https://prove2.me/theorems/21f5d580-1e94-46da-8566-700a53a067a6
-- title:
--   A strict finite graph supergraph has more edges
-- statement:
--   For finite simple graphs on the same vertex type, a strict supergraph has strictly more edges. This isolates the finite counting step used to turn a strict extension into the target's one-edge lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.strict_subgraph_edgeSet_ncard__p2m_8470bdfe_f75c_45f2_9449_e6bb0fb08f8f_a1
    {V : Type} [Fintype V]
    (G K : SimpleGraph V)
    (hsub : G ≤ K)
    (hne : G ≠ K) :
    G.edgeSet.ncard < K.edgeSet.ncard := by sorry
