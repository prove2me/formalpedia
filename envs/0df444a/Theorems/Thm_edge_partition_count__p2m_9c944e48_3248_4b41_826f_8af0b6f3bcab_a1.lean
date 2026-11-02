-- Prove2me | Theorems.Thm_edge_partition_count__p2m_9c944e48_3248_4b41_826f_8af0b6f3bcab_a1
-- name    : edge_partition_count__p2m_9c944e48_3248_4b41_826f_8af0b6f3bcab_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:09:15.949202+00:00
-- url     : https://prove2.me/theorems/4c9d20c0-5d93-440a-a99d-0e5539068656
-- title:
--   Count edges covered by disjoint blocks exactly once
-- statement:
--   If pairwise disjoint finite vertex blocks cover the endpoints of every graph edge, summing, over blocks, the number of graph edges with both endpoints in that block counts every graph edge exactly once.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem edge_partition_count__p2m_9c944e48_3248_4b41_826f_8af0b6f3bcab_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (C : Finset (Finset V))
    (hdisj : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hpair : ∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    (letI : DecidableRel L.Adj := dL;
    (∑ s ∈ C, {e ∈ L.edgeFinset | e.toFinset ⊆ s}.card) = L.edgeFinset.card) := by sorry
