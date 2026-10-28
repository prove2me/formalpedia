-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_9dbc1b44_5e81_4cbc_9338_84418c6013a1
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_9dbc1b44_5e81_4cbc_9338_84418c6013a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:54:51.487747+00:00
-- url     : https://prove2.me/theorems/78babe8f-e579-430d-899d-02fc3c5a98de
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite graphs on the same vertex type, inclusion of all edges of the first graph in the second implies that its edge count is no greater.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edgeSet_ncard_mono_9dbc1b44_5e81_4cbc_9338_84418c6013a1
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) :
    (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by sorry
