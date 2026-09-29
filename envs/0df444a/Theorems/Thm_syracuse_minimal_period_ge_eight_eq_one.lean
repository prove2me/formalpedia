-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_eight_eq_one
-- name    : syracuse_minimal_period_ge_eight_eq_one
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-09T01:43:46.065924+00:00
-- url     : https://prove2.me/theorems/efe4beff-fef3-4f9b-8d8d-1cf81a6649ca
-- title:
--   Exclude nontrivial Syracuse cycles of least period at least eight
-- statement:
--   Let T(n) be the odd part of 3n+1. Suppose m is a positive integer and p is its least positive return time: T iterated p times returns m, and no positive number of steps smaller than p returns m. Under the additional assumption p ≥ 8, prove that m=1. Since 1 itself has least period one, this would rule out the existence of such a cycle. This is the remaining open cycle obligation after excluding least periods one through seven; it is not a claim that the full Collatz conjecture has been proved.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; least-positive-return case split for syracuse_periodic_ge_seven_eq_one (e108a9c0-9ea8-4841-96f2-78bb716d0525), using existing return-time exclusions one through seven.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_minimal_period_ge_eight_eq_one (m p : ℕ) (hm : 0 < m) (hp : 8 ≤ p) (hcyc : syracuseStep^[p] m = m) (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by sorry
