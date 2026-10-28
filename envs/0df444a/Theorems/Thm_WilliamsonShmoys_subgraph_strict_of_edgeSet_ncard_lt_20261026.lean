-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_strict_of_edgeSet_ncard_lt_20261026
-- name    : WilliamsonShmoys.subgraph_strict_of_edgeSet_ncard_lt_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:57:32.306504+00:00
-- url     : https://prove2.me/theorems/867503c8-3d3d-4114-b2f7-7c8287f0038b
-- title:
--   Strict graph inclusion from an edge-count increase
-- statement:
--   For finite simple graphs, inclusion and a strict increase in the number of edges imply strict graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_strict_of_edgeSet_ncard_lt_20261026
    {V : Type} [Fintype V] [DecidableEq V]
    (L M : SimpleGraph V)
    (hLM : L ≤ M)
    (hcard : L.edgeSet.ncard < M.edgeSet.ncard) :
    L < M := by
  sorry
