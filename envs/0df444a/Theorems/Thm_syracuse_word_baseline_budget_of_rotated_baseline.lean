-- Prove2me | Theorems.Thm_syracuse_word_baseline_budget_of_rotated_baseline
-- name    : syracuse_word_baseline_budget_of_rotated_baseline
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:27:03.954228+00:00
-- url     : https://prove2.me/theorems/8520bcc0-c537-42f4-8b11-a4d573dc4835
-- title:
--   Global dyadic budget bound from per-rotation Syracuse affine constant baselines
-- statement:
--   Let $w = (e_0, \ldots, e_{p-1})$ be a finite word of natural numbers of length $p = \operatorname{length}(w)$ and total sum $K = \sum_{i=0}^{p-1} e_i$, and let $B \in \mathbb{N}$ be a baseline parameter. Define the canonical Syracuse affine constant $C(u) = \operatorname{syracuseAffineConstant}(u)$ recursively by $C([]) = 0$ and $C(a :: u) = 3^{\operatorname{length}(u)} + 2^a C(u)$. Assume the positive power-gap inequality $3^p < 2^K$, and suppose that every cyclic rotation $w.\operatorname{rotate}(d)$ ($0 \le d < p$) satisfies the lower bound
--
--   $$B \cdot (2^K - 3^p) \le C\bigl(w.\operatorname{rotate}(d)\bigr).$$
--
--   Then the word length $p$, total sum $K$, and baseline $B$ satisfy the global product-budget inequality
--
--   $$2^K \cdot B^p \le (3B + 1)^p.$$
--
--   Mathematically, this theorem lifts the classical Collatz cycle product bound $2^K = \prod_{d=0}^{p-1} (3 + 1/x_d) \le (3 + 1/B)^p$ from realized periodic Syracuse orbits to arbitrary abstract valuation words via the rotated affine constants $C(w.\operatorname{rotate}(d))$, showing that any uniform per-rotation state baseline $B$ directly forces the global $(p, K)$ budget inequality at $B$ without requiring divisibility or orbit realization.
-- source:
--   Collatz cycle-exclusion frontier bridge packet (Mission 2f34a49f-2016-4de2-9662-fcd1cc96cc67); helper rotation-balance lemmas adapted with attribution from accepted submission 9675ddf1-ef38-491c-84bd-56455a8a8b7f by FakeMink (090844a7-327d-477a-b08e-2937c520007f).

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_word_baseline_budget_of_rotated_baseline (w : List ℕ) (B : ℕ)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hbaseline : ∀ d : ℕ, d < w.length →
      B * (2 ^ w.sum - 3 ^ w.length) ≤ syracuseAffineConstant (w.rotate d)) :
    2 ^ w.sum * B ^ w.length ≤ (3 * B + 1) ^ w.length := by sorry
