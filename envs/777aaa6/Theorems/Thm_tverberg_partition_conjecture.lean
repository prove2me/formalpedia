-- Prove2me | Theorems.Thm_tverberg_partition_conjecture
-- name    : tverberg_partition_conjecture
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:10:26.372319+00:00
-- url     : https://prove2.me/theorems/a9797f49-91cd-42cb-9c34-5dbff79b7a87
-- statement:
--   Tverberg's theorem: Any N=(r-1)(d+1)+1 points in ℝᵈ can be partitioned into r parts whose convex hulls intersect. The topological version (for continuous maps) is disproved for non-prime-power r; open for prime power r ≥ 4.
-- source:
--   https://en.wikipedia.org/wiki/Tverberg%27s_theorem

import Mathlib

import Mathlib

theorem tverberg_partition_conjecture (r d : ℕ) (hr : 2 ≤ r) (hd : 1 ≤ d) :
    ∀ (pts : Fin ((r - 1) * (d + 1) + 1) → EuclideanSpace ℝ (Fin d)),
      ∃ (partition : Fin r → Finset (Fin ((r-1)*(d+1)+1))),
        (∀ i, (partition i).Nonempty) ∧
        Finset.univ = Finset.biUnion Finset.univ partition ∧
        (∀ i j, i ≠ j → Disjoint (partition i) (partition j)) ∧
        (⋂ i : Fin r, convexHull ℝ
          ((partition i).image pts).toSet).Nonempty := by
  sorry
