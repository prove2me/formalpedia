-- Prove2me | Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline
-- name    : syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline
-- status  : Open
-- author  : @FakeMink
-- created : 2026-10-02T14:37:32.103683+00:00
-- url     : https://prove2.me/theorems/9f28e7b8-804f-4efd-83e3-1e68362b2b34
-- title:
--   Remaining primitive-word nondivisibility with every rotated affine state above the certified baseline
-- statement:
--   Let $w=(e_0,\ldots,e_{p-1})$ be a list of positive natural numbers, with $p=\operatorname{length}(w)\ge6291$ and $K=\sum_i e_i$. Assume every proper positive cyclic rotation differs from $w$. Define the canonical affine constant by
--
--   $$C([])=0,\qquad C(a::b)=3^{\operatorname{length}(b)}+2^a C(b).$$
--
--   Retain the power gap, both strict mean conditions, and the exact global budget at $B=2310000$:
--
--   $$3^p<2^K,\qquad200K<317p,\qquad306K<485p,\qquad2^K B^p\le(3B+1)^p.$$
--
--   Put $D=2^K-3^p>0$. Assume additionally that every indexed rotation meets the word-dependent certified-baseline filter:
--
--   $$\forall d\in\{0,\ldots,p-1\},\qquad BD\le C(w.rotate\ d).$$
--
--   Prove
--
--   $$D\nmid C(w).$$
--
--   This is an unresolved restricted arithmetic obligation. The new filter is an explicit premise on arbitrary candidate words, not an assertion that they automatically satisfy it. Its necessity for nontrivial realized cycles follows from a separately Proved finite cycle-state baseline and exact affine divisibility realization. No actual cycle is assumed before divisibility, no larger uncertified baseline is used, and no state upper bound or period cap is introduced. The remaining family and Collatz convergence are not claimed proved.
-- source:
--   Rotated-state child of the current Open exact-budget word frontier https://prove2.me/theorems/63d03529-75b9-4f49-9100-d4a2a787fd66 under the preserved Collatz tail path. Credits Proved finite cycle-state baseline https://prove2.me/theorems/73735589-bbad-479f-8d7e-375fd2f82875 and canonical affine definition https://prove2.me/theorems/864533ea-15c3-4810-a04c-d66a460333b7 . Complementary proof includes the unchanged 387-line rotation-divisibility and exact canonical-quotient realization construction already compiled in accepted sketches9675ddf1 and8c51a6dd, with credit to those constructions and public supports. This formalizes a known word-dependent minimum-state filter, not a global novelty or full parent/tail/Collatz proof claim.

import Mathlib
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6291 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length)
    (hrotatedBaseline : ∀ d : ℕ, d < w.length →
      (2310000 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
        syracuseAffineConstant (w.rotate d)) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
