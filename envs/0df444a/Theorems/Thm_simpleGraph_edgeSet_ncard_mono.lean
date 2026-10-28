-- Prove2me | Theorems.Thm_simpleGraph_edgeSet_ncard_mono
-- name    : simpleGraph_edgeSet_ncard_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:58:11.194059+00:00
-- url     : https://prove2.me/theorems/672d29f5-b1d5-41eb-aecd-1a7829ded033
-- title:
--   Monotonicity of simple graph edge count
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem simpleGraph_edgeSet_ncard_mono
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
