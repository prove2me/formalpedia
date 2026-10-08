-- Prove2me | Theorems.Thm_ChannelContinuity_FiniteAnalyticInputs_threshold_le_of_eventual_sqrt_bound
-- name    : ChannelContinuity.FiniteAnalyticInputs.threshold_le_of_eventual_sqrt_bound
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-07T23:48:17.188275+00:00
-- url     : https://prove2.me/theorems/21324dce-fe13-470c-b2af-8897ffb1b86a
-- title:
--   Testing error below one bounds the finite Rényi threshold
-- statement:
--   Let $(d,f,c,E)$ be finite analytic input data: $d\ge0$, $f$ is monotone on $(1,\infty)$ and bounded below by $d$, $E(n,r)\ge0$, and the package's weak-testing, Rényi-testing, and raw Schatten estimates hold. Here $f$ is the order-dependent scalar divergence, $c$ its finite cap, and $E$ the testing quantity. Set $d_+=\inf_{a>1}f(a)$. If $r\ge0$, $B<1$, and $\sqrt{E(n,r)}\le B$ for all sufficiently large $n$, then
--
--   $$d_+\le r.$$
--
--   This conditional scalar criterion converts a persistent testing error strictly below one into an upper bound on the right-hand threshold; its analytic input package is part of the hypothesis.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/ChannelContinuity/Main.lean#L81-L105

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Monotone
import Definitions.Def_CRCD_ChannelContinuity_Main
import Definitions.Def_CRCD_ChannelContinuity_Parameters
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_ChannelContinuity_ThreePiece

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/










/-!
# Scalar limit argument for Theorem 1

The successive limit passages, testing-threshold argument, and left/right
assembly are proved. `FiniteAnalyticInputs` records the scalar estimates needed
for the finite right-limit argument; its raw Schatten estimate is normalized
here. `QuantumChannelContinuity.QuantumMain` derives that estimate from the
proved operator bounds, and `QuantumChannelContinuity.ContinuityAssembly`
constructs the input record for concrete channels in the finite branch.
`QuantumChannelContinuity.Main` combines the finite and infinite cases with
the proved state-order facts to export the unconditional channel theorem.
-/

open Filter Set
open scoped Topology ENNReal

namespace ChannelContinuity
end ChannelContinuity
open ChannelContinuity

theorem ChannelContinuity.FiniteAnalyticInputs.threshold_le_of_eventual_sqrt_bound
    (h : FiniteAnalyticInputs) {r B : ℝ} (hr : 0 ≤ r) (hBlt : B < 1)
    (hBevent : ∀ᶠ n in atTop, Real.sqrt (h.testing n r) ≤ B) :
    sInf (h.renyi '' Ioi 1) ≤ r := by sorry
