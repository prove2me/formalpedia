-- Prove2me | Theorems.Thm_syracuse_word_length_6956_to_7620_affine_nondivisibility
-- name    : syracuse_word_length_6956_to_7620_affine_nondivisibility
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:33:55.933882+00:00
-- url     : https://prove2.me/theorems/c34e96bc-68cc-4d1a-aba5-fbfda500037d
-- title:
--   Syracuse word affine nondivisibility for periods $6956 \le p < 7621$
-- statement:
--   Let $w = (e_0, \ldots, e_{p-1})$ be a list of positive natural numbers ($e_i > 0$ for all $i$) of length $p = \operatorname{length}(w)$ satisfying $6956 \le p < 7621$ and total sum $K = \sum_{i=0}^{p-1} e_i$. Define the canonical Syracuse affine constant $\operatorname{syracuseAffineConstant}(w)$ recursively by $\operatorname{syracuseAffineConstant}([]) = 0$ and $\operatorname{syracuseAffineConstant}(a :: b) = 3^{\operatorname{length}(b)} + 2^a \operatorname{syracuseAffineConstant}(b)$. Assume the positive power-gap condition $3^p < 2^K$, the strict rational upper bound $306 K < 485 p$, and the global budget inequality
--
--   $$2^K \cdot 2{,}310{,}000^p \le (3 \cdot 2{,}310{,}000 + 1)^p.$$
--
--   Then the candidate cycle denominator $D = 2^K - 3^p$ does not divide $\operatorname{syracuseAffineConstant}(w)$:
--
--   $$(2^K - 3^p) \nmid \operatorname{syracuseAffineConstant}(w).$$
--
--   This theorem eliminates the entire period band $6956 \le p < 7621$ from the Collatz cycle-exclusion frontier: unimodular Farey trapping inside $(1054/665,\, 7863/4961)$ uniquely forces $(p, K) = (6956, 11025)$, where the mechanical rotation bound is strictly smaller than $2{,}855{,}820 \cdot (2^{11025} - 3^{6956}) \le 2{,}887{,}463 \cdot (2^{11025} - 3^{6956})$.
-- source:
--   Collatz cycle-exclusion frontier period-6956-to-7620 elimination (Mission 2f34a49f-2016-4de2-9662-fcd1cc96cc67), combining the unimodular Farey certificate 1054/665 < K/p < 7863/4961 (adapted from submission 148bed53-8007-4529-90a5-00c1158db5de by user FakeMink, 090844a7-327d-477a-b08e-2937c520007f), the mechanical rotation bound (theorem 695ac23a-1e9a-48a2-a6b8-70a72d754213), kernel evaluation of the (6956, 11025) mechanical numerator (adapted from submission 5e67e1b7-cc46-4084-9654-6621f1460052 by user a9c5687f-bf1a-4250-b67a-cad2d27a67f1), and syracuse_word_affine_nondivisibility_of_some_rotation_lt_2887463.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_word_length_6956_to_7620_affine_nondivisibility (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlarge : 6956 ≤ w.length)
    (hsmall : w.length < 7621)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
