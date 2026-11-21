-- Prove2me | Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_sparse_8286
-- name    : syracuse_primitive_word_affine_nondivisibility_sparse_8286
-- status  : Open
-- author  : @yuzhou
-- created : 2026-11-20T10:42:37.999085+00:00
-- url     : https://prove2.me/theorems/af726993-2622-416b-bbdd-684b3e5621a6
-- title:
--   Syracuse affine nondivisibility for the remaining lengths from 7621
-- statement:
--   Let $w$ be a primitive word of positive Syracuse valuations, with length $p$ and sum $K$. Retain all hypotheses of the [parent theorem](https://prove2.me/theorems/28dac570-bf9f-46f8-a8d3-e94ccc8bf7ca), including the affine bound for every rotation at baseline 2,887,463. Suppose also that either $(p,K)=(7621,12079)$ or $p$ is at least 8286. Does the cycle denominator fail to divide the affine constant of $w$?
-- source:
--   Refinement of the parent theorem using syracuse_word_baseline_budget_of_rotated_baseline and an exact power comparison.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_affine_nondivisibility_sparse_8286 (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 7621 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length)
    (hrotatedBaseline : ∀ d : ℕ, d < w.length →
      (2887463 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
        syracuseAffineConstant (w.rotate d))
    (hsparse : (w.length = 7621 ∧ w.sum = 12079) ∨ 8286 ≤ w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
