-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_ncard_mono_euler_20261028
-- name    : WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono_euler_20261028
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:21:59.310232+00:00
-- url     : https://prove2.me/theorems/0e536ddf-1b0b-4bd7-9750-78d0d44c57dd
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For a finite vertex type, inclusion of simple graphs implies monotonicity of the cardinalities of their edge sets. This follows by showing edge-set inclusion from `hHG`, then applying finite-set cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono_euler_20261028
    {V : Type} [Fintype V]
    (H G : SimpleGraph V)
    (hHG : H ≤ G) :
    H.edgeSet.ncard ≤ G.edgeSet.ncard := by sorry
