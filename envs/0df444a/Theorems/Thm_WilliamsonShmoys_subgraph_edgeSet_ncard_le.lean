-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_le
-- name    : WilliamsonShmoys.subgraph_edgeSet_ncard_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:09:14.986031+00:00
-- url     : https://prove2.me/theorems/6d8c4749-0c98-4276-a9e4-179708fc1275
-- title:
--   Edge count is monotone under subgraph inclusion
-- statement:
--   For finite graphs on the same vertex type, inclusion of adjacency relations implies inclusion of their edge sets, hence monotonicity of the finite set cardinality. This is independent of planarity and discharges the parent’s edge-count comparison. A proof route is to show edge-set inclusion from hMH and apply finite-set cardinality monotonicity; finiteness follows from Fintype V.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edgeSet_ncard_le
    {V : Type} [Fintype V] [DecidableEq V]
    (M H : SimpleGraph V) (hMH : M ≤ H) :
    Set.ncard M.edgeSet ≤ Set.ncard H.edgeSet := by sorry
