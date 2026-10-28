-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_mono_8575ae1d_620b_40d7_9b25_8ae2db919063
-- name    : WilliamsonShmoys.edge_count_mono_8575ae1d_620b_40d7_9b25_8ae2db919063
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:27:33.492154+00:00
-- url     : https://prove2.me/theorems/1f9a7240-d778-4998-994d-9eb27736aa87
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, inclusion of graphs implies that the edge-set cardinality cannot decrease.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_mono_8575ae1d_620b_40d7_9b25_8ae2db919063
    {V : Type} [Fintype V] [DecidableEq V]
    (Q R : SimpleGraph V)
    (hQR : Q ≤ R) :
    Q.edgeSet.ncard ≤ R.edgeSet.ncard := by sorry
