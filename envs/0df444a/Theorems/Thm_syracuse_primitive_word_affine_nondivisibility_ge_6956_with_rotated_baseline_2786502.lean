-- Prove2me | Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_ge_6956_with_rotated_baseline_2786502
-- name    : syracuse_primitive_word_affine_nondivisibility_ge_6956_with_rotated_baseline_2786502
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T15:10:00.590653+00:00
-- url     : https://prove2.me/theorems/f9fd04d9-1a91-4015-8f1e-d0e842ccf6be
-- title:
--   Rotated-baseline primitive-word affine nondivisibility for period at least 6956 at baseline 2,786,502
-- statement:
--   Let $w = (e_0, \ldots, e_{p-1})$ be a list of positive natural numbers ($e_i > 0$ for all $i$) with period $p = \operatorname{length}(w) \ge 6956$ and total valuation sum $K = \sum_{i=0}^{p-1} e_i$. Assume $w$ is aperiodic under proper cyclic rotations ($w.\operatorname{rotate}(d) \ne w$ for all $0 < d < p$), and define the canonical Syracuse affine constant $\operatorname{syracuseAffineConstant}(w)$ by $\operatorname{syracuseAffineConstant}([]) = 0$ and $\operatorname{syracuseAffineConstant}(a :: b) = 3^{\operatorname{length}(b)} + 2^a \operatorname{syracuseAffineConstant}(b)$. Assume the power-gap and mean-exponent inequalities together with the global budget inequality
--
--   $$3^p < 2^K, \qquad 200 K < 317 p, \qquad 306 K < 485 p, \qquad 2^K \cdot 2310000^p \le (3 \cdot 2310000 + 1)^p,$$
--
--   and assume that every cyclic rotation $w.\operatorname{rotate}(d)$ ($0 \le d < p$) satisfies the upgraded certified baseline bound
--
--   $$2786502 \cdot (2^K - 3^p) \le \operatorname{syracuseAffineConstant}(w.\operatorname{rotate}(d)).$$
--
--   Then the cycle denominator $D = 2^K - 3^p$ does not divide $\operatorname{syracuseAffineConstant}(w)$:
--
--   $$(2^K - 3^p) \nmid \operatorname{syracuseAffineConstant}(w).$$
--
--   This open frontier obligation advances the Collatz cycle-exclusion branch past the sparse-period disjunction $p = 6291 \lor p \ge 6956$ (theorem 0ddfc585-79b5-4904-8288-32ed0e3bd173) by eliminating $p = 6291$ and simultaneously upgrading the per-rotation state baseline from $2{,}310{,}000$ to $2{,}786{,}502$.
-- source:
--   Collatz cycle-exclusion frontier refinement of syracuse_primitive_word_affine_nondivisibility_with_rotated_baseline_sparse_period (0ddfc585-79b5-4904-8288-32ed0e3bd173) after eliminating period 6291 and applying syracuse_no_cycle_below_2786502 (8b82562a-08bf-4b83-a7b3-36f0e888a07f).

import Mathlib
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_affine_nondivisibility_ge_6956_with_rotated_baseline_2786502 (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6956 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length)
    (hrotatedBaseline : ∀ d : ℕ, d < w.length →
      (2786502 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
        syracuseAffineConstant (w.rotate d)) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
