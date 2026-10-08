-- Prove2me | Definitions.Def_CRCD_ChannelContinuity_Parameters
-- name    : CRCD_ChannelContinuity_Parameters
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:44:58.920993+00:00
-- url     : https://prove2.me/theorems/828399b4-877c-4b27-8ff3-1a2fd360f466
-- title:
--   Raw three-term Schatten expression
-- statement:
--   For a natural block length $n$ and real parameters $t,r,D_+,C,b,\varepsilon$, define the raw scalar right-hand side by
--
--   $$\begin{aligned}S_{\mathrm{raw}}(n,t,r,D_+,C,b,\varepsilon)={}&(1+b)^{1-t/n}(2^{nr})^{t/(2n)}\\&+(b+\varepsilon)^{1-t/n}\bigl(4\,2^{n(D_++1/t^2)}\bigr)^{t/(2n)}\\&+\varepsilon^{1-t/n}\bigl(4\,2^{n(C+1)}\bigr)^{t/(2n)}.\end{aligned}$$
--
--   The powers and divisions use Lean's total real operations, so this is a definition even at $n=0$ or $t=0$. Its intended analytic applications impose positive block and parameter conditions and nonnegative error terms. The expression retains the three completely positive domination weights before normalization by the threshold factor; it supplies the raw estimate field in the finite scalar input record.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/ChannelContinuity/Parameters.lean#L20-L99

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_CRCD_ChannelContinuity_ThreePiece

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Parameters and scalar normalization in the three-piece estimate

This file verifies the order choice `α = n / (n - t)` and the base-two
power algebra used to normalize the exponentiated Schatten bound.
-/

namespace ChannelContinuity

/-- The order chosen in the manuscript is strictly greater than one. -/
theorem renyi_order_gt_one {n t : ℝ} (ht : 0 < t) (htn : t < n) :
    1 < n / (n - t) := by
  apply (one_lt_div (sub_pos.mpr htn)).2
  linarith

/-- The near-one range suffices for the first limit: after `n ≥ 2t`, the
chosen Rényi order is at most two. -/
theorem renyi_order_le_two {n t : ℝ} (htn : t < n) (h2tn : 2 * t ≤ n) :
    n / (n - t) ≤ 2 := by
  apply (div_le_iff₀ (sub_pos.mpr htn)).2
  linarith

/-- The corresponding Schatten interpolation parameter is exactly `t / n`. -/
theorem renyi_order_fraction {n t : ℝ} (ht : 0 < t) (htn : t < n) :
    (n / (n - t) - 1) / (n / (n - t)) = t / n := by
  have hn : n ≠ 0 := ne_of_gt (lt_trans ht htn)
  have hnt : n - t ≠ 0 := ne_of_gt (sub_pos.mpr htn)
  field_simp
  ring













/-- The exponentiated Schatten estimate with the three manuscript CP weights,
before division by the threshold factor. -/
noncomputable def rawSchattenRhs (n : ℕ) (t r dPlus cap b ε : ℝ) : ℝ :=
  (1 + b) ^ (1 - t / n) * ((2 : ℝ) ^ ((n : ℝ) * r)) ^ (t / n / 2) +
  (b + ε) ^ (1 - t / n) *
    ((4 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (dPlus + 1 / (t * t)))) ^ (t / n / 2) +
  ε ^ (1 - t / n) *
    ((4 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (cap + 1))) ^ (t / n / 2)





end ChannelContinuity


