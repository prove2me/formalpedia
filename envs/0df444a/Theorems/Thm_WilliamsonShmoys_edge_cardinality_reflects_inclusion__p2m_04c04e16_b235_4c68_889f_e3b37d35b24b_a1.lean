-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_cardinality_reflects_inclusion__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
-- name    : WilliamsonShmoys.edge_cardinality_reflects_inclusion__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:45.455387+00:00
-- url     : https://prove2.me/theorems/78bec2a9-c2f4-48fb-957e-d5426d117493
-- title:
--   Equal-or-smaller edge count forces reverse inclusion
-- statement:
--   For finite simple graphs, if every edge of K is an edge of L and K has at least as many edges as L, then every edge of L is already in K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_cardinality_reflects_inclusion__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
    {V : Type} [Fintype V]
    (K L : SimpleGraph V)
    (hKL : ∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v)
    (hcount : K.edgeSet.ncard ≥ L.edgeSet.ncard) :
    ∀ u v, L.Adj u v → K.Adj u v := by sorry
