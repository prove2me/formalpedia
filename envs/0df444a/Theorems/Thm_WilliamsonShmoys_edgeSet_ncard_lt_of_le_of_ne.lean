-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_lt_of_le_of_ne
-- name    : WilliamsonShmoys.edgeSet_ncard_lt_of_le_of_ne
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:41:29.589036+00:00
-- url     : https://prove2.me/theorems/f960fbd0-43b1-4043-adcf-7f3a55ad712e
-- title:
--   Strict edge-count increase for a proper finite simple-graph supergraph
-- statement:
--   If one finite simple graph is included in another and they are unequal, the larger graph has strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edgeSet_ncard_lt_of_le_of_ne
    {V : Type} [Fintype V] [LinearOrder V]
    (L M : SimpleGraph V) (hLM : L ≤ M) (hne : M ≠ L) :
    L.edgeSet.ncard < M.edgeSet.ncard := by sorry
