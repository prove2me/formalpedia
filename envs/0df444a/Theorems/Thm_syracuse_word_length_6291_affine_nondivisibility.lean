-- Prove2me | Theorems.Thm_syracuse_word_length_6291_affine_nondivisibility
-- name    : syracuse_word_length_6291_affine_nondivisibility
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T15:09:57.702+00:00
-- url     : https://prove2.me/theorems/a067b6fb-742b-437c-a2ba-19bee400d90a
-- title:
--   Syracuse word affine nondivisibility at exact period 6291
-- statement:
--   Let $w = (e_0, \ldots, e_{p-1})$ be a list of positive natural numbers ($e_i > 0$ for all $i$) of exact length $p = \operatorname{length}(w) = 6291$ and total sum $K = \sum_{i=0}^{p-1} e_i$. Define the canonical Syracuse affine constant $\operatorname{syracuseAffineConstant}(w)$ recursively by $\operatorname{syracuseAffineConstant}([]) = 0$ and $\operatorname{syracuseAffineConstant}(a :: b) = 3^{\operatorname{length}(b)} + 2^a \operatorname{syracuseAffineConstant}(b)$. Assume the positive power-gap condition $3^p < 2^K$ and the strict rational upper bound $306 K < 485 p$. Then
--
--   $$(2^K - 3^p) \nmid \operatorname{syracuseAffineConstant}(w).$$
--
--   This theorem eliminates the isolated convergent period $p = 6291$ (for which the power-gap and mean conditions uniquely force $K = 9971$) from the Collatz Syracuse cycle-exclusion frontier by combining the mechanical rotation bound (theorem 695ac23a-1e9a-48a2-a6b8-70a72d754213), the strict mechanical numerator bound at $(p, K) = (6291, 9971)$ (theorem ab3539bc-2660-453c-ac0c-d3f902b3d85c), and the certified Syracuse cycle exclusion below $2{,}786{,}502$ (theorem 8b82562a-08bf-4b83-a7b3-36f0e888a07f).
-- source:
--   Collatz cycle-exclusion frontier period-6291 elimination (Mission 2f34a49f-2016-4de2-9662-fcd1cc96cc67), combining 695ac23a-1e9a-48a2-a6b8-70a72d754213, ab3539bc-2660-453c-ac0c-d3f902b3d85c, and 8b82562a-08bf-4b83-a7b3-36f0e888a07f.

import Mathlib
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_word_length_6291_affine_nondivisibility (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : w.length = 6291)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlowSharp : 306 * w.sum < 485 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
