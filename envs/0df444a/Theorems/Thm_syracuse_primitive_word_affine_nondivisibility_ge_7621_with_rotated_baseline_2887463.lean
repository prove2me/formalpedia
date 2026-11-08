-- Prove2me | Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_ge_7621_with_rotated_baseline_2887463
-- name    : syracuse_primitive_word_affine_nondivisibility_ge_7621_with_rotated_baseline_2887463
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T13:33:54.517086+00:00
-- url     : https://prove2.me/theorems/28dac570-bf9f-46f8-a8d3-e94ccc8bf7ca
-- title:
--   Rotated-baseline primitive-word affine nondivisibility for period at least $7621$ at baseline $2{,}887{,}463$
-- statement:
--   Let $w = (e_0, \ldots, e_{p-1})$ be a list of positive natural numbers ($e_i > 0$ for all $i$) with period $p = \operatorname{length}(w) \ge 7621$ and total valuation sum $K = \sum_{i=0}^{p-1} e_i$. Assume $w$ is aperiodic under proper cyclic rotations ($w.\operatorname{rotate}(d) \ne w$ for all $0 < d < p$), and define the canonical Syracuse affine constant $\operatorname{syracuseAffineConstant}(w)$ by $\operatorname{syracuseAffineConstant}([]) = 0$ and $\operatorname{syracuseAffineConstant}(a :: b) = 3^{\operatorname{length}(b)} + 2^a \operatorname{syracuseAffineConstant}(b)$. Assume the power-gap and mean-exponent inequalities together with the global budget inequality
--
--   $$3^p < 2^K, \qquad 200 K < 317 p, \qquad 306 K < 485 p, \qquad 2^K \cdot 2{,}310{,}000^p \le (3 \cdot 2{,}310{,}000 + 1)^p,$$
--
--   and assume that every cyclic rotation $w.\operatorname{rotate}(d)$ ($0 \le d < p$) satisfies the upgraded certified baseline bound
--
--   $$2{,}887{,}463 \cdot (2^K - 3^p) \le \operatorname{syracuseAffineConstant}(w.\operatorname{rotate}(d)).$$
--
--   Then the cycle denominator $D = 2^K - 3^p$ does not divide $\operatorname{syracuseAffineConstant}(w)$:
--
--   $$(2^K - 3^p) \nmid \operatorname{syracuseAffineConstant}(w).$$
--
--   This open frontier obligation advances the Collatz cycle-exclusion branch from $p \ge 6956$ at baseline $2{,}786{,}502$ (`syracuse_primitive_word_affine_nondivisibility_ge_6956_with_rotated_baseline_2786502`, theorem f9fd04d9-1a91-4015-8f1e-d0e842ccf6be) to $p \ge 7621$ at baseline $2{,}887{,}463$.
-- source:
--   Collatz cycle-exclusion frontier refinement of syracuse_primitive_word_affine_nondivisibility_ge_6956_with_rotated_baseline_2786502 (f9fd04d9-1a91-4015-8f1e-d0e842ccf6be) after eliminating periods 6956 ≤ p < 7621 and upgrading the cycle-exclusion baseline to 2,887,463.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_affine_nondivisibility_ge_7621_with_rotated_baseline_2887463 (w : List ℕ)
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
        syracuseAffineConstant (w.rotate d)) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
