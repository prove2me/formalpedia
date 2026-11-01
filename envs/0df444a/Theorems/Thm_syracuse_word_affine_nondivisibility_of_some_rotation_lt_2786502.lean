-- Prove2me | Theorems.Thm_syracuse_word_affine_nondivisibility_of_some_rotation_lt_2786502
-- name    : syracuse_word_affine_nondivisibility_of_some_rotation_lt_2786502
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T15:10:07.867234+00:00
-- url     : https://prove2.me/theorems/7a625c3b-7bd7-4914-a3d0-90107c396bf8
-- title:
--   Syracuse word affine nondivisibility under a rotation below the 2,786,502 cycle threshold
-- statement:
--   Let $w = (e_0, \ldots, e_{p-1})$ be a list of positive natural numbers ($e_i > 0$ for all $i$) of length $p = \operatorname{length}(w)$ and total sum $K = \sum_{i=0}^{p-1} e_i$. Define the canonical Syracuse affine constant $\operatorname{syracuseAffineConstant}(w)$ recursively by $\operatorname{syracuseAffineConstant}([]) = 0$ and $\operatorname{syracuseAffineConstant}(a :: b) = 3^{\operatorname{length}(b)} + 2^a \operatorname{syracuseAffineConstant}(b)$. Assume the positive power-gap condition $3^p < 2^K$, the strict rational upper bound $306 K < 485 p$, and the existence of a cyclic rotation index $0 \le d < p$ satisfying
--
--   $$\operatorname{syracuseAffineConstant}(w.\operatorname{rotate}(d)) < 2786502 \cdot (2^K - 3^p).$$
--
--   Then the cycle denominator $D = 2^K - 3^p$ does not divide the affine constant:
--
--   $$(2^K - 3^p) \nmid \operatorname{syracuseAffineConstant}(w).$$
--
--   This theorem provides a reusable bridge between upper bounds on rotated Syracuse affine constants (such as the mechanical rotation bound) and the certified finite Syracuse cycle exclusion threshold $2{,}786{,}502$, enabling both fixed-period exclusions and baseline upgrades across the Collatz cycle-exclusion frontier.
-- source:
--   Collatz cycle-exclusion frontier reduction (Mission 2f34a49f-2016-4de2-9662-fcd1cc96cc67), combining syracuse_positive_word_affine_divisibility_realizes_syracuse_cycle (78b082d4-594c-4179-8e50-8e372a26c563) and syracuse_no_cycle_below_2786502 (8b82562a-08bf-4b83-a7b3-36f0e888a07f).

import Mathlib
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_word_affine_nondivisibility_of_some_rotation_lt_2786502 (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hsmallRot : ∃ d : ℕ, d < w.length ∧
      syracuseAffineConstant (w.rotate d) < 2786502 * (2 ^ w.sum - 3 ^ w.length)) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
