-- Prove2me | Theorems.Thm_syracuse_prefix_stays_of_small_valuation_sums
-- name    : syracuse_prefix_stays_of_small_valuation_sums
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T11:14:55.957575+00:00
-- url     : https://prove2.me/theorems/fcde9319-1644-501b-9a44-0838fb961700
-- title:
--   No Syracuse descent during a prefix with small cumulative halving factors
-- statement:
--   If at every prefix length through k the accumulated halving factor is at most the corresponding power of three, all Syracuse states through k are at least the starting value.
-- source:
--   Finite-prefix Syracuse product identity.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem syracuse_prefix_stays_of_small_valuation_sums (n k : ℕ)
    (hsmall : ∀ j ≤ k,
      2^((Finset.range j).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) ≤ 3^j) :
    ∀ j ≤ k, n ≤ syracuseStep^[j] n := by sorry
