-- Prove2me | Theorems.Thm_syracuse_word_affine_nondivisibility_of_some_rotation_lt_2887463
-- name    : syracuse_word_affine_nondivisibility_of_some_rotation_lt_2887463
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:33:54.3385+00:00
-- url     : https://prove2.me/theorems/c2919b55-8bd5-4f2d-a208-a825fb0029a9
-- title:
--   Syracuse word affine nondivisibility under a rotation below the $2{,}887{,}463$ cycle threshold
-- statement:
--   Let $w = (e_0, \ldots, e_{p-1})$ be a list of positive natural numbers ($e_i > 0$ for all $i$) of length $p = \operatorname{length}(w)$ and total sum $K = \sum_{i=0}^{p-1} e_i$. Define the canonical Syracuse affine constant $\operatorname{syracuseAffineConstant}(w)$ recursively by $\operatorname{syracuseAffineConstant}([]) = 0$ and $\operatorname{syracuseAffineConstant}(a :: b) = 3^{\operatorname{length}(b)} + 2^a \operatorname{syracuseAffineConstant}(b)$. Assume the positive power-gap condition $3^p < 2^K$, the strict rational upper bound $306 K < 485 p$, and the existence of a cyclic rotation index $0 \le d < p$ satisfying
--
--   $$\operatorname{syracuseAffineConstant}(w.\operatorname{rotate}(d)) < 2{,}887{,}463 \cdot (2^K - 3^p).$$
--
--   Then the cycle denominator $D = 2^K - 3^p$ does not divide the affine constant:
--
--   $$(2^K - 3^p) \nmid \operatorname{syracuseAffineConstant}(w).$$
--
--   This theorem bridges upper bounds on rotated Syracuse affine constants (such as the mechanical rotation bound) with the upgraded finite Syracuse cycle-exclusion threshold $2{,}887{,}463$, enabling the elimination of period $p = 6956$ and the baseline upgrade to $2{,}887{,}463$ across the Collatz cycle-exclusion frontier.
-- source:
--   Collatz cycle-exclusion frontier reduction (Mission 2f34a49f-2016-4de2-9662-fcd1cc96cc67), upgrading syracuse_word_affine_nondivisibility_of_some_rotation_lt_2786502 (7a625c3b-7bd7-4914-a3d0-90107c396bf8, adapted from submission 26ec230a-e6f3-4394-ab2b-3cc335cd34ad by user FakeMink, 090844a7-327d-477a-b08e-2937c520007f) with syracuse_no_cycle_below_2887463.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_word_affine_nondivisibility_of_some_rotation_lt_2887463 (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hsmallRot : ∃ d : ℕ, d < w.length ∧
      syracuseAffineConstant (w.rotate d) < 2887463 * (2 ^ w.sum - 3 ^ w.length)) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
