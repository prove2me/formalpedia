-- Prove2me | Theorems.Thm_syracuse_primitive_word_residual_period_coordinates_at_1241513984
-- name    : syracuse_primitive_word_residual_period_coordinates_at_1241513984
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-11-25T14:51:49.403978+00:00
-- url     : https://prove2.me/theorems/31e42a4c-297d-4340-9e15-9bed5006f80d
-- title:
--   Remaining primitive word obstruction at the 1,241,513,984 cutoff
-- statement:
--   Retain every hypothesis of the [residual problem at the 247,463,936 cutoff](https://prove2.me/theorems/06111f80-6da0-4594-807b-89983611efc6) on a primitive word $w$ of positive Syracuse valuations, with length $p=|w|$ and sum $K=\sum w$. Assume in addition that
--
--   $$(p,K)=a\,(31867,50508)+b\,(47468,75235)$$
--
--   for some positive integers $a,b$, so that $p\ge 79{,}335$. Prove that the cycle denominator $2^{K}-3^{p}$ does not divide the Syracuse affine constant of $w$.
--
--   This is an open obligation, not an established cycle exclusion: it is what remains of the cycle branch once every cycle element is known to be at least $1{,}241{,}513{,}984$. Words whose $(p,K)$ is not of this form are excluded by the [period-coordinate theorem at 1,241,513,984](https://prove2.me/theorems/a093b898-08bc-5e1e-8112-2e286d7af04d). The hypotheses of the parent are kept verbatim; the new hypothesis implies the two older coordinate hypotheses.
-- source:
--   Residual child of Prove2me theorem 06111f80-6da0-4594-807b-89983611efc6 (syracuse_primitive_word_residual_period_coordinates_at_247463936) in the Collatz Conjecture mission; coordinate form after S. Eliahou, Discrete Mathematics 118 (1993), 45-56, Theorem 1.1.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_residual_period_coordinates_at_1241513984 (w : List ℕ)
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
      ((w.rotate i).take n).sum + 2 ≤ ((w.rotate j).take n).sum)
    (hcoords247 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      w.length = 31867*a + 15601*b ∧ w.sum = 50508*a + 24727*b)
    (hcoords1241 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      w.length = 31867*a + 47468*b ∧ w.sum = 50508*a + 75235*b) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
