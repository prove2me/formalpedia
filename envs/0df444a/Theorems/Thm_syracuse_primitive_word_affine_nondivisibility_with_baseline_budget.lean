-- Prove2me | Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_with_baseline_budget
-- name    : syracuse_primitive_word_affine_nondivisibility_with_baseline_budget
-- status  : Open
-- author  : @FakeMink
-- created : 2026-10-02T04:01:36.879509+00:00
-- url     : https://prove2.me/theorems/63d03529-75b9-4f49-9100-d4a2a787fd66
-- title:
--   Remaining primitive-word nondivisibility under the exact certified-baseline budget
-- statement:
--   Let $w=(e_0,\ldots,e_{p-1})$ be a finite list of positive natural numbers, with $p=\operatorname{length}(w)\ge6291$ and $K=\sum_i e_i$. Suppose every proper positive left cyclic rotation differs from $w$. Define the canonical affine constant by
--
--   $$C([])=0,\qquad C(a::b)=3^{\operatorname{length}(b)}+2^a C(b).$$
--
--   Assume all prior gap and mean conditions
--
--   $$3^p<2^K,\qquad200K<317p,\qquad306K<485p,$$
--
--   and the additional exact integer budget at $B=2310000$,
--
--   $$2^K B^p\le(3B+1)^p.$$
--
--   Prove
--
--   $$2^K-3^p\nmid C(w).$$
--
--   This is an unresolved restricted arithmetic obligation, not an established nondivisibility theorem. It retains every premise of the preceding 485/306 word problem and adds only the exact budget. That budget is supplied for arbitrary candidate words; its necessity for hypothetical nontrivial realized cycles uses a separately Proved finite cycle-state baseline. No cycle is assumed to exist without the affine divisibility condition, no larger uncertified baseline is used, and no state upper bound, upper period cap, or all-rotation state filter is imposed. The remaining family is not claimed impossible and the tail remains unproved.
-- source:
--   Exact-budget child of the current Open primitive-word frontier https://prove2.me/theorems/594d7b4f-9d54-4068-b855-f25de426937b under the preserved tail-to-word path of the Collatz mission. Credits the actual Proved finite cycle-state baseline https://prove2.me/theorems/73735589-bbad-479f-8d7e-375fd2f82875 and public minimum-product bound https://prove2.me/theorems/514577b7-9148-4a35-a0b2-80ac16b8b322 . The complementary reduction instantiates the explicit-baseline exact-budget helper at2310000 and includes the complete corrected realization construction previously compiled in accepted sketch9675ddf1-ef38-491c-84bd-56455a8a8b7f. Credits canonical affine definition https://prove2.me/theorems/864533ea-15c3-4810-a04c-d66a460333b7 . This expresses a known product-envelope restriction exactly, not a claim of global mathematical novelty or a completed arithmetic/parent/Collatz proof.

import Mathlib
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_affine_nondivisibility_with_baseline_budget (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6291 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
