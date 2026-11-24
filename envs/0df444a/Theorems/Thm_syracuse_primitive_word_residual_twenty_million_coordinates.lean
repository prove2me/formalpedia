-- Prove2me | Theorems.Thm_syracuse_primitive_word_residual_twenty_million_coordinates
-- name    : syracuse_primitive_word_residual_twenty_million_coordinates
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T10:36:52.405162+00:00
-- url     : https://prove2.me/theorems/4c78e8bc-6a5e-4296-856d-b824327aebc3
-- title:
--   Remaining primitive word obstruction at the 20,971,520 cutoff
-- statement:
--   In the [previous primitive word problem](https://prove2.me/theorems/89e43502-29fa-4758-8be2-9c4cffa08d66), strengthen the coordinate assumption to $10b<3a$. Thus $(|w|,\sum w)=a(665,1054)+b(10946,17349)$ with positive $a,b$ and $2a<15b$. Prove that the cycle denominator does not divide the affine constant of $w$.
-- source:
--   Refines https://prove2.me/theorems/89e43502-29fa-4758-8be2-9c4cffa08d66 using syracuse_nontrivial_period_coordinates_at_twenty_million.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_residual_twenty_million_coordinates (w : List ℕ)
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
      w.length = 665*a + 10946*b ∧ w.sum = 1054*a + 17349*b ∧ 2*a < 15*b ∧ 10*b < 3*a) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
