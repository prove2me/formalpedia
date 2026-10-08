-- Prove2me | Theorems.Thm_ChannelContinuity_two_term_bound_of_three_piece
-- name    : ChannelContinuity.two_term_bound_of_three_piece
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-07T23:45:36.324999+00:00
-- url     : https://prove2.me/theorems/4a114783-1441-4e30-8d3a-60b3fe670b8e
-- title:
--   Limit of the normalized three-piece scalar bound
-- statement:
--   Let $b_n,\varepsilon_n\ge0$ be real sequences, let $B,t,r,d_+,c$ be real, and suppose $b_n\le B$ eventually and $\varepsilon_n\to0$. Put
--
--   $$R_n=(1+b_n)^{1-t/n}2^{-t(d_+-r)/2}+2^{t/n}(b_n+\varepsilon_n)^{1-t/n}2^{1/(2t)}+2^{t/n}\varepsilon_n^{1-t/n}2^{t(c+1-d_+)/2}.$$
--
--   If $1\le R_n$ for all sufficiently large $n$, then
--
--   $$1\le(1+B)2^{-t(d_+-r)/2}+B2^{1/(2t)}.$$
--
--   The parameter $t$ is fixed; no uniform convergence in $t$ or positivity assumption on $t$ is imposed. This is the block-length limit of the three-piece estimate.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/ChannelContinuity/ThreePiece.lean#L34-L86

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

theorem ChannelContinuity.two_term_bound_of_three_piece
    {b ε : ℕ → ℝ} {B t r dPlus cap : ℝ}
    (hb : ∀ n, 0 ≤ b n) (hε : ∀ n, 0 ≤ ε n)
    (hB : ∀ᶠ n in atTop, b n ≤ B)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      1 ≤ threePieceRhs n t r dPlus cap (b n) (ε n)) :
    1 ≤ (1 + B) * (2 : ℝ) ^ (-t * (dPlus - r) / 2) +
      B * (2 : ℝ) ^ (1 / (2 * t)) := by sorry
