-- Prove2me | Theorems.Thm_syracuse_primitive_word_nondivisibility_after_adjacent_period_sieve
-- name    : syracuse_primitive_word_nondivisibility_after_adjacent_period_sieve
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T07:49:28.028864+00:00
-- url     : https://prove2.me/theorems/055539bb-518e-4e7d-869c-639609b16db6
-- title:
--   Remaining Syracuse word obstruction after the adjacent-pair period test
-- statement:
--   Let $w$ be a primitive cyclic word of positive valuations, $p$ its length, $K$ the sum of its entries, and $A(w)$ its Syracuse affine constant. Retain the hypotheses of the [parent word problem](https://prove2.me/theorems/475518d9-1e4f-4b12-a93e-4fb02eef8946): $p\ge7621$, $3^p<2^K$, $200K<317p$, $306K<485p$, $2^K\,2310000^p\le6930001^p$, and $A(v)\ge2887463(2^K-3^p)$ for every rotation $v$ of $w$. Assume $(p,K)=(7621,12079)$ or $p\ge8286$. Put
--   $$L=\left\lfloor\frac{50508p}{31867}\right\rfloor+1.$$
--   Assume the previous period condition $92011L<145834p$ and the additional condition $99991L<158482p$ obtained from adjacent orbit entries. Show that $2^K-3^p$ does not divide $A(w)$.
-- source:
--   Residual case of https://prove2.me/theorems/475518d9-1e4f-4b12-a93e-4fb02eef8946 after applying syracuse_cycle_eq_one_of_adjacent_period_sieve and the positive affine word realization theorem.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_nondivisibility_after_adjacent_period_sieve (w : List ℕ)
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
    (hadj : 99991 * (50508 * w.length / 31867 + 1) < 158482 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
