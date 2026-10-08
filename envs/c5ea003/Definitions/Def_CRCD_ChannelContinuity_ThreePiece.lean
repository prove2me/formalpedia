-- Prove2me | Definitions.Def_CRCD_ChannelContinuity_ThreePiece
-- name    : CRCD_ChannelContinuity_ThreePiece
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T22:49:37.770661+00:00
-- url     : https://prove2.me/theorems/be545dc8-7f94-44b5-b48d-f26b0c989497
-- title:
--   Normalized three-piece scalar expression
-- statement:
--   For $n\in\mathbb N$ and real $t,r,D_+,C,b,\varepsilon$, define
--
--   $$\begin{aligned}S_3(n,t,r,D_+,C,b,\varepsilon)={}&(1+b)^{1-t/n}2^{-t(D_+-r)/2}\\&+2^{t/n}(b+\varepsilon)^{1-t/n}2^{1/(2t)}\\&+2^{t/n}\varepsilon^{1-t/n}2^{t(C+1-D_+)/2}.\end{aligned}$$
--
--   Here $b$ and $\varepsilon$ represent square roots of two testing errors, $r$ is the lower testing rate, $D_+$ is the limiting order threshold, and $C$ is a finite cap in the applications. The definition itself imposes no inequalities on its real arguments and uses total real powers and division. This is the normalized scalar form of the three-piece bound used in the successive block-length and parameter limits; helper results that assume an upper bound by this expression retain that assumption explicitly.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/ChannelContinuity/ThreePiece.lean#L27-L32

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

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

/-- Right-hand side of the paper's normalized three-piece estimate. -/
noncomputable def threePieceRhs (n : ℕ) (t r dPlus cap b ε : ℝ) : ℝ :=
  (1 + b) ^ (1 - t / n) * (2 : ℝ) ^ (-t * (dPlus - r) / 2) +
  (2 : ℝ) ^ (t / n) * (b + ε) ^ (1 - t / n) * (2 : ℝ) ^ (1 / (2 * t)) +
  (2 : ℝ) ^ (t / n) * ε ^ (1 - t / n) *
    (2 : ℝ) ^ (t * (cap + 1 - dPlus) / 2)





end ChannelContinuity


