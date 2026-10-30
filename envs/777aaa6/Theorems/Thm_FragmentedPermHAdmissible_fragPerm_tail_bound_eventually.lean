-- Prove2me | Theorems.Thm_FragmentedPermHAdmissible_fragPerm_tail_bound_eventually
-- name    : FragmentedPermHAdmissible.fragPerm_tail_bound_eventually
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:43:06.436743+00:00
-- url     : https://prove2.me/theorems/94acf9d5-36c4-4643-999e-d2b64e5aa33c
-- title:
--   Supporting lemma: fragPerm tail bound eventually
-- statement:
--   Supporting lemma from AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermHAdmissible.lean.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma fragPerm_tail_bound_eventually :
--       ∀ᶠ r : ℝ in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
--         fragPermSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
--           ‖saddleGAt fragPermFun r n θ‖ ≤ fragPermTailE r
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/FragmentedPermHAdmissible.lean#L8. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Fragmented permutations: finite-radius H-admissible saddle data

Fragmented permutations are the labelled class `SET(SEQ_{\ge 1}(Z))`, with EGF
`exp (z / (1 - z))`.  This file packages the finite-radius Hayman data for the
committed `HAdmissible` bridge.  The saddle regime is `r -> 1-`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

open FragmentedPermHAdmissible

theorem FragmentedPermHAdmissible.fragPerm_tail_bound_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
      fragPermSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt fragPermFun r n θ‖ ≤ fragPermTailE r := by sorry
