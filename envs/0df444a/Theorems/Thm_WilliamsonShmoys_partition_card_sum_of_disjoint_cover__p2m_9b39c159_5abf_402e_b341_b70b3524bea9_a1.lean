-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_card_sum_of_disjoint_cover__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1
-- name    : WilliamsonShmoys.partition_card_sum_of_disjoint_cover__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:23:53.127001+00:00
-- url     : https://prove2.me/theorems/74e5b976-931d-4a07-9f91-22945814e572
-- title:
--   Cardinality sum for a disjoint finite cover
-- statement:
--   For a pairwise-disjoint family of finite vertex subsets indexed by `V` whose union covers `V`, the sum of their cardinalities equals the cardinality of `V`. This removes the cover-counting step from the target; it can be proved by applying the finite disjoint-union cardinality formula to `Finset.univ.biUnion C` and rewriting with `hcover`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem WilliamsonShmoys.partition_card_sum_of_disjoint_cover__p2m_9b39c159_5abf_402e_b341_b70b3524bea9_a1
    {V : Type} [Fintype V] [LinearOrder V] (C : V → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : Finset.univ.biUnion C = Finset.univ) :
    (∑ i : V, (C i).card) = Fintype.card V := by sorry
