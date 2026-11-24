-- Prove2me | Theorems.Thm_syracuse_primitive_word_residual_eight_million_period_sieve
-- name    : syracuse_primitive_word_residual_eight_million_period_sieve
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T08:12:50.375104+00:00
-- url     : https://prove2.me/theorems/d1678ccb-a2e9-47ff-834f-b37b28d280f6
-- title:
--   Remaining Syracuse word obstruction after the 8,388,608 cutoff
-- statement:
--   Keep all the assumptions of the [three-entry residual word problem](https://prove2.me/theorems/8c018c44-08ba-40b6-b2e5-ef0d57d499c8). Let $p=|w|$ and $L=\lfloor50508p/31867\rfloor+1$. In addition suppose $73297L<116173p$. Show that $2^{\sum w}-3^p$ does not divide the Syracuse affine constant of $w$. This is the remaining case after applying the $2^{23}$ cutoff and three-entry period bound.
-- source:
--   Refines https://prove2.me/theorems/8c018c44-08ba-40b6-b2e5-ef0d57d499c8 by the period test syracuse_cycle_eq_one_of_eight_million_triple_sieve.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_residual_eight_million_period_sieve (w : List ℕ)
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
    (hlarge : 73297 * (50508 * w.length / 31867 + 1) < 116173 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
