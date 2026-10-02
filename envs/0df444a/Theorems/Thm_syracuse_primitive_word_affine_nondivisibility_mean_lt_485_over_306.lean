-- Prove2me | Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_mean_lt_485_over_306
-- name    : syracuse_primitive_word_affine_nondivisibility_mean_lt_485_over_306
-- status  : Open
-- author  : @FakeMink
-- created : 2026-10-02T01:22:22.721988+00:00
-- url     : https://prove2.me/theorems/594d7b4f-9d54-4068-b855-f25de426937b
-- title:
--   Remaining affine nondivisibility obstruction for primitive words with mean valuation below 485/306
-- statement:
--   Let $w=(e_0,\ldots,e_{p-1})$ be a list of positive natural numbers with $p=\operatorname{length}(w)\ge6291$ and $K=\sum_i e_i$. Suppose every proper positive left cyclic rotation differs from $w$: $\operatorname{rotate}_d(w)\ne w$ for $0<d<p$. Define the canonical affine constant by
--
--   $$C([])=0,\qquad C(a::b)=3^{\operatorname{length}(b)}+2^a C(b).$$
--
--   Assume the explicit power gap and mean conditions
--
--   $$3^p<2^K,\qquad 200K<317p,\qquad306K<485p.$$
--
--   Prove
--
--   $$2^K-3^p\nmid C(w).$$
--
--   This is an unresolved restricted arithmetic obligation, not a proved nondivisibility result. It preserves every hypothesis of the earlier primitive low-mean word problem and adds the sharper strict mean condition. The earlier mean inequality is retained explicitly even though the sharper one implies it. The power gap is supplied for arbitrary words; it is not silently inferred from a hypothetical orbit. No finite state bound, upper period cap, cycle-minimum assumption or all-rotation baseline filter is imposed. A separate conditional reduction can eliminate the complementary high-mean band only using actually verified word realization and the sharper high-mean cycle theorem. This problem does not assert that the remaining family is impossible or that the full tail is proved.
-- source:
--   Sharper restricted child of the prospective existing primitive-word obligation syracuse_primitive_low_mean_word_affine_nondivisibility under the Collatz mission's low-mean tail https://prove2.me/theorems/47d69530-0846-4d09-a212-6a25ea00aa9e . Derived complementary split485*p<=306*K or306*K<485*p; high-band elimination includes the complete positive-word realization proof in the integrated reduction and imports syracuse_cycle_eq_one_of_mean_valuation_ge_485_over_306 only after its actual Proved verification. Credits the canonical affine definition https://prove2.me/theorems/864533ea-15c3-4810-a04c-d66a460333b7 and the existing high-mean proof https://prove2.me/theorems/da5c0141-3f01-4271-8ca2-cebe7d4d407e . This is a conjectural contribution obligation, not a result quoted as established in the literature or a claim of global mathematical novelty.

import Mathlib
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_affine_nondivisibility_mean_lt_485_over_306 (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6291 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
