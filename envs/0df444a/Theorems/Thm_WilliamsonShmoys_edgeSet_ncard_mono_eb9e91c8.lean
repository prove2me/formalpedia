-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_eb9e91c8
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_eb9e91c8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:31:06.494866+00:00
-- url     : https://prove2.me/theorems/c6978780-7bdd-4ad0-87ee-068548205080
-- title:
--   Monotonicity of finite edge-set cardinality
-- statement:
--   For finite simple graphs on the same vertex type, inclusion of graphs implies monotonicity of edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono_eb9e91c8
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
