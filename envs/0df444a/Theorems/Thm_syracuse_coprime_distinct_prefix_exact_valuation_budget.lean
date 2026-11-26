-- Prove2me | Theorems.Thm_syracuse_coprime_distinct_prefix_exact_valuation_budget
-- name    : syracuse_coprime_distinct_prefix_exact_valuation_budget
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:45:50.336523+00:00
-- url     : https://prove2.me/theorems/e43c05da-e39f-4490-9e1d-149fb3e6a999
-- title:
--   Exact valuation budget for distinct Syracuse states coprime to six
-- statement:
--   Let a Syracuse orbit start at a positive integer coprime to six. Suppose its first k states (excluding the endpoint) are pairwise distinct and at least B > 0, and let A be the sum of the first k valuations. Set d(i) = B + 6 floor(i/2) + 2 (i mod 2). Then 2^A times the endpoint times the product of the d(i) is at most the starting value times the product of 3 d(i)+1, with both products over i<k.
-- source:
--   Extends the sorted-product method of Prove2Me submission 8c188af5-f0ae-4343-b8c0-4a1447008e8b from least-period cycles to arbitrary distinct segments and uses the mod-six restriction.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem syracuse_coprime_distinct_prefix_exact_valuation_budget (n B k : ℕ)
    (hB : 0 < B) (hodd : n % 2 = 1) (hthree : ¬ 3 ∣ n)
    (hfloor : ∀ i < k, B ≤ syracuseStep^[i] n)
    (hinj : Set.InjOn (fun i : ℕ => syracuseStep^[i] n) {i | i < k}) :
    2^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) *
        syracuseStep^[k] n * (∏ i ∈ Finset.range k, (B+6*(i/2)+2*(i%2))) ≤
      n * (∏ i ∈ Finset.range k, (3*(B+6*(i/2)+2*(i%2))+1)) := by sorry
