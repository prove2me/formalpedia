-- Prove2me | Definitions.Def_Geometry_KakeyaKatzTaoSumset
-- name    : Geometry_KakeyaKatzTaoSumset
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:25.795762+00:00
-- url     : https://prove2.me/theorems/279f220a-0b77-43a1-9123-58c2b898230a
-- title:
--   Aether Catalog definitions — Geometry_KakeyaKatzTaoSumset
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.KakeyaKatzTaoSumset`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/KakeyaKatzTaoSumset.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The additive-combinatorics bridge: sumset growth (Katz–Tao framework)

The Katz–Tao approach to the Kakeya problem reduces dimension lower bounds to
*sum–difference* estimates in additive combinatorics: a Kakeya set forces a
configuration whose iterated sumsets must grow, and quantitative growth
translates back into a dimension bound.  The cleanest exactly-provable engine of
this kind is the **Cauchy–Davenport** inequality in the prime cyclic group
`ZMod p`.

This file proves the iterated-sumset growth law that powers such arguments:

  `|kA| ≥ min(p, k·(|A| − 1) + 1)`  for every nonempty `A ⊆ ZMod p`,

by induction on `k` using Cauchy–Davenport, and deduces the qualitative
corollary that any set with at least two elements *generates the whole group*
under enough additions (`kA = ZMod p` once `k ≥ p − 1`).  This is the discrete
analogue of "a Kakeya set, after enough additive combination, fills space".

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): Cauchy–Davenport should iterate to a linear-in-`k`
  growth `|kA| ≳ k|A|` until saturation at `p`.  Predicted exact bound
  `min(p, k(|A|−1)+1)`.
* Experiment (Experimenter): defined `sumIter A k` by recursion (`A + (A + …)`),
  proved nonemptiness by induction, and ran the induction on `k`, feeding
  `ZMod.cauchy_davenport` at each step.  The `min` and `ℕ`-subtraction bookkeeping
  was the only real obstacle (handled with `omega`).
* Analysis (Analyst): the bound is sharp for arithmetic progressions
  (`A = {0,1,…,m−1}` gives `kA = {0,…,k(m−1)}` of size exactly `k(m−1)+1` while
  that stays `< p`).  Saturation happens at `k = ⌈(p−1)/(|A|−1)⌉`.
* Critique (Critic): the corollary `sumset_generates` is non-vacuous — it needs
  `|A| ≥ 2`; for `|A| = 1` (singleton) `kA` is a singleton forever, which the
  bound `min(p, k·0+1) = 1` correctly predicts.  No hidden triviality: the proof
  uses genuine induction and Cauchy–Davenport, not `decide`.
* Synthesis (PI): `card_sumIter_ge` is the headline growth law;
  `sumset_generates` is the saturation corollary tying it to "filling space".
-/

open Finset Pointwise

namespace KakeyaKatzTao

/-- Iterated sumset: `sumIter A k = A + A + ⋯ + A` (`k+1` copies, so
`sumIter A 0 = A`). -/
def sumIter {p : ℕ} (A : Finset (ZMod p)) : ℕ → Finset (ZMod p)
  | 0 => A
  | (k + 1) => A + sumIter A k



/-
The iterated sumset of a nonempty set is nonempty.
-/

/-
Any subset of `ZMod p` has at most `p` elements.
-/

/-
**Iterated Cauchy–Davenport growth.** For a prime `p` and nonempty
`A ⊆ ZMod p`, the `k`-fold sumset satisfies `|kA| ≥ min(p, k(|A|−1)+1)`.
-/

/-
**Saturation / generation.** If `A ⊆ ZMod p` has at least two elements, then
once `k ≥ p − 1` the iterated sumset is all of `ZMod p` (it has `p` elements).
-/

end KakeyaKatzTao


