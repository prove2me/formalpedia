-- Prove2me | Theorems.Thm_syracuse_primitive_word_nondivisibility_after_triple_period_sieve
-- name    : syracuse_primitive_word_nondivisibility_after_triple_period_sieve
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T07:57:56.194922+00:00
-- url     : https://prove2.me/theorems/8c018c44-08ba-40b6-b2e5-ef0d57d499c8
-- title:
--   Remaining Syracuse word obstruction after the three-entry period test
-- statement:
--   Retain all the assumptions of the [parent word problem](https://prove2.me/theorems/055539bb-518e-4e7d-869c-639609b16db6). In particular $w$ is a primitive word of positive valuations, $p=|w|\ge7621$, $K=\sum w$, $3^p<2^K$, $200K<317p$, $306K<485p$, and $2^K 2310000^p\le6930001^p$. Every rotation $v$ satisfies $A(v)\ge2887463(2^K-3^p)$ for the Syracuse affine constant $A$. Assume $(p,K)=(7621,12079)$ or $p\ge8286$. For $L=\lfloor50508p/31867\rfloor+1$, the inherited period restrictions are $92011L<145834p$ and $99991L<158482p$.
--
--   In addition suppose $69866L<110735p$. Show that $2^K-3^p$ does not divide $A(w)$. This is the remaining case after the three-entry estimate.
-- source:
--   Refinement of https://prove2.me/theorems/055539bb-518e-4e7d-869c-639609b16db6 by syracuse_cycle_eq_one_of_triple_period_sieve and the positive affine word realization theorem.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_nondivisibility_after_triple_period_sieve (w : List ℕ)
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
    (htriple : 69866 * (50508 * w.length / 31867 + 1) < 110735 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
