-- Prove2me | Theorems.Thm_sum_sup_sub_le
-- name    : sum_sup_sub_le
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T23:43:50.799643+00:00
-- url     : https://prove2.me/theorems/eb9fe89a-a409-4b77-bbfa-357ee1736e99
-- title:
--   Bousquet condition (3): $\sum_k (Z-Z_k)\le Z$ for suprema of sums
-- statement:
--   Bousquet's structural condition (3) for suprema of sums. Let $Z=\max_s\sum_i X_{i,s}$ over a nonempty finite family and $Z_k=\max_s\sum_{i\ne k}X_{i,s}$ the leave-coordinate-$k$-out supremum, with all $X_{i,s}\ge 0$. Then $\sum_k (Z-Z_k)\le Z$. Holds for the supremum of sums with NO monotonicity / self-bounding assumption beyond $X\ge 0$ — the 'drop one coordinate from the maximiser' estimate the entropy-method route needs.
-- source:
--   Bousquet 2002 C.R.Acad.Sci.334:495-500 §3 (condition (3)); Klein–Rio 2005 Ann.Probab.33 §3 (arXiv:math/0506594); BLM Concentration Inequalities §11.2.

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
open Finset

theorem sum_sup_sub_le
    {ι S : Type*} [DecidableEq ι] [Fintype ι] [Fintype S] [Nonempty S]
    (X : ι → S → ℝ) (hX : ∀ i s, 0 ≤ X i s)
    (Z : ℝ) (Zk : ι → ℝ)
    (hZ : Z = Finset.univ.sup' Finset.univ_nonempty (fun s => ∑ i, X i s))
    (hZk : ∀ k, Zk k = Finset.univ.sup' Finset.univ_nonempty (fun s => ∑ i ∈ Finset.univ.erase k, X i s)) :
    ∑ k, (Z - Zk k) ≤ Z := by sorry
