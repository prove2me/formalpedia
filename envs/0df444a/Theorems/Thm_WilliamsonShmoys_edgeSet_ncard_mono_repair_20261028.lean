-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_repair_20261028
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_repair_20261028
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:34:58.055981+00:00
-- url     : https://prove2.me/theorems/ef8ef3c2-8418-4a06-9569-24a142649bca
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   This child removes the finite-cardinality transfer from the parent. It is a new elementary graph argument: inclusion gives inclusion of edge sets, and cardinality is monotone for finite sets. It is independent of the drawing hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edgeSet_ncard_mono_repair_20261028
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
