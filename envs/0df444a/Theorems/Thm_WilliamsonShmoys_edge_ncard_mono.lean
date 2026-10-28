-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_mono
-- name    : WilliamsonShmoys.edge_ncard_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:06:35.340363+00:00
-- url     : https://prove2.me/theorems/219cdb23-91bd-4008-9837-6ffc0bceefa9
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite vertex types, including every edge of one graph in another cannot decrease the edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_ncard_mono
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
