-- Prove2me | Definitions.Def_CRCD_ChannelContinuity_Main
-- name    : CRCD_ChannelContinuity_Main
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:46:46.032307+00:00
-- url     : https://prove2.me/theorems/51d6d556-f994-404a-a6d5-ac795960bb65
-- title:
--   Scalar hypotheses for the finite right-continuity argument
-- statement:
--   The scalar interface consists of a real number $d$, a real-valued function $R$ of the Rényi order, a real cap $C$, and a testing function $T:\mathbb N\times\mathbb R\to\mathbb R$. Write $D_+=\inf_{a>1}R(a)$. The record requires $d\ge0$, monotonicity of $R$ on $(1,\infty)$, $d\le R(a)$ for $a>1$, and $T(n,r)\ge0$. Its two testing hypotheses are
--
--   $$T(n,r)\le\frac d r+\frac1{nr}\quad(r>0,\ n\ge1),\qquad T(n,\ell)\le2^{-n(a-1)(\ell-R(a))}\quad(a>1,\ R(a)<\ell,\ n\ge1).$$
--
--   The remaining hypothesis is an explicit raw Schatten estimate: for $0\le r<D_+$, $t\ge1$, $t<n$, and $2t\le n$,
--
--   $$2^{tD_+/2}\le S_{\mathrm{raw}}\!\left(n,t,r,D_+,C,\sqrt{T(n,r)},\sqrt{T(n,D_++t^{-2})}\right).$$
--
--   Here $S_{\mathrm{raw}}$ is the scalar three-term expression defined by the parameter interface. The infimum is Lean's total real infimum; boundedness facts needed for later reasoning are derived under the record's hypotheses. These fields are assumptions of scalar helper results. For the concrete quantum theorem, separate proved channel estimates construct the record; defining this record does not itself discharge its hypotheses.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/ChannelContinuity/Main.lean#L34-L63

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

/-- The finite-case scalar quantities and estimates.

Intended interpretations:
* `d` = regularized channel relative entropy;
* `renyi a` = regularized sandwiched channel Rényi divergence;
* `cap` = finite channel max-relative entropy;
* `testing n r` = hockey-stick divergence at threshold `2^(n*r)`.

The scalar hypotheses are explicit fields; the concrete channel assembly
constructs them from proved results.
-/
structure FiniteAnalyticInputs where
  d : ℝ
  renyi : ℝ → ℝ
  cap : ℝ
  testing : ℕ → ℝ → ℝ
  d_nonneg : 0 ≤ d
  order_mono : MonotoneOn renyi (Ioi 1)
  relative_le_renyi : ∀ a, 1 < a → d ≤ renyi a
  testing_nonneg : ∀ n r, 0 ≤ testing n r
  weak_testing : ∀ r, 0 < r → ∀ n : ℕ, 0 < n →
    testing n r ≤ d / r + 1 / ((n : ℝ) * r)
  renyi_testing : ∀ a, 1 < a → ∀ ell, renyi a < ell → ∀ n : ℕ, 0 < n →
    testing n ell ≤ (2 : ℝ) ^ (-(n : ℝ) * (a - 1) * (ell - renyi a))
  raw_schatten : ∀ r, 0 ≤ r → r < sInf (renyi '' Ioi 1) →
    ∀ t : ℝ, 1 ≤ t → ∀ n : ℕ, t < (n : ℝ) → 2 * t ≤ (n : ℝ) →
      (2 : ℝ) ^ (t * sInf (renyi '' Ioi 1) / 2) ≤
      rawSchattenRhs n t r (sInf (renyi '' Ioi 1)) cap
        (Real.sqrt (testing n r))
        (Real.sqrt (testing n (sInf (renyi '' Ioi 1) + 1 / (t * t))))













end ChannelContinuity


