-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch5_Meromorphic_Alignments_alignmentCount_div_factorial_isEquivalent
-- name    : AnalyticCombinatorics.Ch5.Meromorphic.Alignments.alignmentCount_div_factorial_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T21:21:39.668075+00:00
-- url     : https://prove2.me/theorems/a6576ca5-36ba-4647-bdae-caf320626cff
-- title:
--   Factorial-normalized alignment counts
-- statement:
--   An alignment is the source labelled sequence of nonempty labelled cycles of atoms: its finite size-$n$ fibre has count $A_n$. With $\rho=1-e^{-1}$, $$\frac{A_n}{n!}\sim\frac{\rho^{-n}}{e-1}.$$ The formal conclusion embeds the rational normalized count into $\mathbb C$ and uses the source complex constants.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/Alignments.lean#L710. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_Alignments
import Mathlib
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

open AnalyticCombinatorics
open AnalyticCombinatorics.Ch5
open AnalyticCombinatorics.Ch5.Meromorphic
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

open AnalyticCombinatorics.Ch1

theorem AnalyticCombinatorics.Ch5.Meromorphic.Alignments.alignmentCount_div_factorial_isEquivalent :
    (fun n : ℕ =>
      algebraMap ℚ ℂ ((alignmentCount n : ℚ) / (n.factorial : ℚ)))
      ~[atTop] (fun n : ℕ => alignmentConstant * rho⁻¹ ^ n) := by sorry
