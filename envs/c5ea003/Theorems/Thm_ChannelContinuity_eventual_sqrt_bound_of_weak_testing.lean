-- Prove2me | Theorems.Thm_ChannelContinuity_eventual_sqrt_bound_of_weak_testing
-- name    : ChannelContinuity.eventual_sqrt_bound_of_weak_testing
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-07T23:45:16.912928+00:00
-- url     : https://prove2.me/theorems/2023e8e2-65a1-4c9b-97f6-7f2923d8342e
-- title:
--   An eventual square-root error bound from weak testing
-- statement:
--   Let $E:\mathbb N\to\mathbb R$ and let $0\le d<r$. Suppose that, for every positive integer $n$,
--
--   $$E(n)\le\frac dr+\frac1{nr}.$$
--
--   Then there is a real number $B$ with $0\le B<1$ such that
--
--   $$\sqrt{E(n)}\le B\qquad\text{for all sufficiently large }n.$$
--
--   No nonnegativity assumption on $E$ is required; the real square root uses its totalized convention on negative inputs. This provides the eventual scalar error bound needed at every rate above $d$.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/ChannelContinuity/ThreePiece.lean#L88-L111

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_CRCD_ChannelContinuity_ThreePiece

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/






/-!
# The first limit in the three-piece argument

This file proves the real-analysis passage from equation `threepiecebound` to
equation `contradiction` in the supplied manuscript.  The operator-theoretic
three-piece estimate is a hypothesis, not an axiom or a proved quantum fact.

An eventual bound `b n ≤ B < 1` replaces a limsup.  Continuity of real powers
at exponent one also covers zero bases, so no nonzero-error assumption is used.
-/

open Filter Topology

namespace ChannelContinuity
end ChannelContinuity
open ChannelContinuity

theorem ChannelContinuity.eventual_sqrt_bound_of_weak_testing
    {E : ℕ → ℝ} {d r : ℝ} (hd : 0 ≤ d) (hdr : d < r)
    (hweak : ∀ n : ℕ, 0 < n → E n ≤ d / r + 1 / ((n : ℝ) * r)) :
    ∃ B : ℝ, 0 ≤ B ∧ B < 1 ∧ ∀ᶠ n in atTop, Real.sqrt (E n) ≤ B := by sorry
