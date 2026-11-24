-- Prove2me | Theorems.Thm_syracuse_primitive_word_residual_unbalanced_windows
-- name    : syracuse_primitive_word_residual_unbalanced_windows
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T11:11:33.25631+00:00
-- url     : https://prove2.me/theorems/267d318c-30be-48c0-a20c-ed8b9a458d6b
-- title:
--   Remaining Syracuse word obstruction for unbalanced cyclic windows
-- statement:
--   Retain all hypotheses of the primitive word obstruction at the 20,971,520 cutoff. Assume in addition that two nonempty proper cyclic windows of equal length have valuation sums differing by at least two. Prove that the positive cycle denominator does not divide the affine constant of $w$.
-- source:
--   Refines https://prove2.me/theorems/4c78e8bc-6a5e-4296-856d-b824327aebc3 using syracuse_primitive_cycle_word_has_unbalanced_windows.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_residual_unbalanced_windows (w : List ℕ)
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
    (hsparse : (w.length = 7621 ∧ w.sum = 12079) ∨ 8286 ≤ w.length)
    (hcandidate : 92011 * (50508 * w.length / 31867 + 1) < 145834 * w.length)
    (hadj : 99991 * (50508 * w.length / 31867 + 1) < 158482 * w.length)
    (htriple : 69866 * (50508 * w.length / 31867 + 1) < 110735 * w.length)
    (hlarge : 73297 * (50508 * w.length / 31867 + 1) < 116173 * w.length)
    (hcoords : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      w.length = 665*a + 10946*b ∧ w.sum = 1054*a + 17349*b ∧ 2*a < 15*b ∧ 10*b < 3*a)
    (hunbalanced : ∃ i j n : ℕ, i < w.length ∧ j < w.length ∧ 0 < n ∧ n < w.length ∧
      ((w.rotate i).take n).sum + 2 ≤ ((w.rotate j).take n).sum) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
