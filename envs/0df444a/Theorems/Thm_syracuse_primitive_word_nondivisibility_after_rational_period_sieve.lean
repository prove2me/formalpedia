-- Prove2me | Theorems.Thm_syracuse_primitive_word_nondivisibility_after_rational_period_sieve
-- name    : syracuse_primitive_word_nondivisibility_after_rational_period_sieve
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T07:40:00.368503+00:00
-- url     : https://prove2.me/theorems/475518d9-1e4f-4b12-a93e-4fb02eef8946
-- title:
--   Syracuse word obstruction at periods surviving the rational test
-- statement:
--   Let $w$ be a primitive cyclic word of positive Syracuse valuations, $p$ its length, $K$ the sum of its entries, and $A(w)$ its Syracuse affine constant. Suppose $p\ge7621$, $3^p<2^K$, $200K<317p$, $306K<485p$, and
--   $$2^K\,2310000^p\le6930001^p.$$
--   For every rotation $v$ of $w$, assume $A(v)\ge2887463(2^K-3^p)$. As in the [parent problem](https://prove2.me/theorems/af726993-2622-416b-bbdd-684b3e5621a6), assume either $(p,K)=(7621,12079)$ or $p\ge8286$.
--
--   Restrict to the lengths satisfying
--   $$92011\left(\left\lfloor\frac{50508p}{31867}\right\rfloor+1\right)<145834p.$$
--   Is $A(w)$ indivisible by $2^K-3^p$ for every such word? This length restriction carries forward the parent assumptions and discards lengths already excluded by the rational period test.
-- source:
--   Residual case of https://prove2.me/theorems/af726993-2622-416b-bbdd-684b3e5621a6 obtained using syracuse_cycle_eq_one_of_rational_period_sieve and the positive affine word realization theorem.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_nondivisibility_after_rational_period_sieve (w : List ℕ)
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
    (hcandidate : 92011 * (50508 * w.length / 31867 + 1) < 145834 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
