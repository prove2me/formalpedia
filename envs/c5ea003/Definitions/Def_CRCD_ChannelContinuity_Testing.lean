-- Prove2me | Definitions.Def_CRCD_ChannelContinuity_Testing
-- name    : CRCD_ChannelContinuity_Testing
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T22:49:41.258161+00:00
-- url     : https://prove2.me/theorems/21df0c3c-bb05-4d82-99e1-176ccad7ea87
-- title:
--   Scalar testing bounds from entropy and Rényi inequalities
-- statement:
--   Let $n,r,d,p,a,\ell,\alpha,J$ be real numbers, where $J$ is a testing payoff and $J\le p$. If $n>0$, $r>0$, and $(nr)p-1\le nd$, then
--
--   $$
--   J\le \frac d r+\frac1{nr}.
--   $$
--
--   The same conclusion holds when the entropy inequality is assumed only in the case $J>0$, provided additionally that $d\ge0$. If $\alpha>1$, $p>0$, and
--
--   $$
--   n\ell+\frac{\log_2 p}{\alpha-1}\le na,
--   $$
--
--   then $J\le2^{-n(\alpha-1)(\ell-a)}$. A companion formulation assumes this logarithmic inequality only when $J>0$; the conclusion then holds without a separate positivity premise on $p$. All logarithms in these testing bounds have base two.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/ChannelContinuity/Testing.lean#L25-L128

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/








/-!
# Scalar reductions of the binary testing inequalities

These lemmas prove the algebra, base-two exponentiation, and passage to a
supremum in the manuscript's testing lemma. The quantum binary data-processing
bounds are explicit hypotheses; this file does not identify abstract scalars
with quantum relative entropies.
-/

namespace ChannelContinuity

/-- The relative-entropy binary testing inequality bounds the testing payoff.
The real variable `n` allows direct specialization to positive natural block
sizes without making the elementary calculation depend on coercions. -/
theorem weak_testing_bound {n r d p objective : ℝ}
    (hn : 0 < n) (hr : 0 < r)
    (hdata : (n * r) * p - 1 ≤ n * d) (hobjective : objective ≤ p) :
    objective ≤ d / r + 1 / (n * r) := by
  have hp : p ≤ (n * d + 1) / (n * r) :=
    (le_div_iff₀ (mul_pos hn hr)).2 (by nlinarith)
  calc
    objective ≤ p := hobjective
    _ ≤ (n * d + 1) / (n * r) := hp
    _ = d / r + 1 / (n * r) := by
      field_simp [ne_of_gt hn, ne_of_gt hr]

/-- Base-two exponentiation turns the Rényi binary data-processing inequality
into the high-rate exponential estimate. Positivity of `n` or of the rate gap
is not needed for this algebraic implication. -/
theorem high_testing_bound {n alpha a ell p objective : ℝ}
    (halpha : 1 < alpha) (hp : 0 < p)
    (hdata : n * ell + (1 / (alpha - 1)) * Real.logb 2 p ≤ n * a)
    (hobjective : objective ≤ p) :
    objective ≤ (2 : ℝ) ^ (-n * (alpha - 1) * (ell - a)) := by
  have ha : 0 < alpha - 1 := sub_pos.mpr halpha
  have hlogdiv : Real.logb 2 p / (alpha - 1) ≤ n * a - n * ell := by
    rw [div_eq_mul_inv]
    simpa only [one_div, mul_comm] using
      (show (1 / (alpha - 1)) * Real.logb 2 p ≤ n * a - n * ell by linarith)
  have hlog := (div_le_iff₀ ha).1 hlogdiv
  have hpbound : p ≤ (2 : ℝ) ^ (-n * (alpha - 1) * (ell - a)) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hp).1
    nlinarith
  exact hobjective.trans hpbound







/-- In the hockey-stick argument the binary inequality is only needed for
strictly positive payoff. Nonpositive payoffs already satisfy the bound. -/
theorem high_testing_bound_of_positive_payoff {n alpha a ell p objective : ℝ}
    (halpha : 1 < alpha) (hobjective : objective ≤ p)
    (hdata : 0 < objective →
      n * ell + (1 / (alpha - 1)) * Real.logb 2 p ≤ n * a) :
    objective ≤ (2 : ℝ) ^ (-n * (alpha - 1) * (ell - a)) := by
  by_cases hpos : 0 < objective
  · exact high_testing_bound halpha (hpos.trans_le hobjective) (hdata hpos) hobjective
  · exact (le_of_not_gt hpos).trans (Real.rpow_nonneg (by norm_num) _)



/-- The weak estimate likewise only needs binary data processing on testers
whose hockey-stick payoff is positive. -/
theorem weak_testing_bound_of_positive_payoff {n r d p objective : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hd : 0 ≤ d) (hobjective : objective ≤ p)
    (hdata : 0 < objective → (n * r) * p - 1 ≤ n * d) :
    objective ≤ d / r + 1 / (n * r) := by
  by_cases hpos : 0 < objective
  · exact weak_testing_bound hn hr (hdata hpos) hobjective
  · apply (le_of_not_gt hpos).trans
    exact add_nonneg (div_nonneg hd hr.le)
      (div_nonneg zero_le_one (mul_pos hn hr).le)



end ChannelContinuity


