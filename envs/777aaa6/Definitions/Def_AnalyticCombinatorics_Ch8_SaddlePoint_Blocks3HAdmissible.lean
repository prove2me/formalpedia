-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3HAdmissible
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3HAdmissible
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T02:43:39.096505+00:00
-- url     : https://prove2.me/theorems/a284e8df-c325-4645-83ba-1016c005da6e
-- title:
--   Size-at-most-three block coefficients and cubic saddle data
-- statement:
--   `CombClass.parts123` is the class with exactly one structure of each size \(1,2,3\) and none of any other size; `CombClass.blocks3` is its labelled set class, so a size-\(n\) object is a partition of the \(n\) labels into blocks of sizes at most three. For \(n\in\mathbb N\), `blocks3CoeffR n` is the real number \(\texttt{blocks3.counts}(n)/n!\). The bundle also defines the complex function \(F(z)=\exp(z+z^2/2+z^3/6)\) as `blocks3Fun`, the real polynomials \(A(r)=r+r^2+r^3/2\) and \(B(r)=r+2r^2+3r^3/2\) as `blocks3SaddleAReal` and `blocks3SaddleBReal`, and `blocks3SaddleRadius n`, a nonnegative real \(r_n\) with \(A(r_n)=n\), chosen from the included existence lemma `blocks3SaddleAReal_exists_of_nonneg`.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/Blocks3HAdmissible.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Blocks of size at most three: H-admissible saddle data

This file records the Hayman data for the EGF
`exp (z + z^2/2 + z^3/6)`, the labelled SET class whose components have
sizes `1`, `2`, or `3`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The class with one component of each size `1`, `2`, and `3`. -/
def CombClass.parts123 : CombClass where
  Obj n := Fin (if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 1 else 0)
  finObj _ := inferInstance

/-- Set partitions whose blocks have size at most `3`: `SET(parts123)`. -/
abbrev CombClass.blocks3 : CombClass :=
  CombClass.parts123.set

end AnalyticCombinatorics.Ch1

namespace Blocks3HAdmissible

abbrev blocks3CoeffR (n : ℕ) : ℝ :=
  (AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) / n.factorial

/-- The analytic function `exp (z + z^2/2 + z^3/6)`. -/
abbrev blocks3Fun (z : ℂ) : ℂ :=
  Complex.exp (z + z ^ 2 / 2 + z ^ 3 / 6)

/-- Continuous saddle mean, `a(r)=r+r^2+r^3/2`. -/
def blocks3SaddleAReal (r : ℝ) : ℝ :=
  r + r ^ 2 + r ^ 3 / 2

/-- Continuous saddle variance scale, `b(r)=r+2r^2+3r^3/2`. -/
def blocks3SaddleBReal (r : ℝ) : ℝ :=
  r + 2 * r ^ 2 + 3 * r ^ 3 / 2

lemma blocks3SaddleAReal_exists_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ∃ r : ℝ, 0 ≤ r ∧ blocks3SaddleAReal r = x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · refine ⟨0, by norm_num, ?_⟩
    simp [blocks3SaddleAReal]
  · have hcont : ContinuousOn blocks3SaddleAReal (Set.Icc (0 : ℝ) x) := by
      unfold blocks3SaddleAReal
      fun_prop
    have hleft : blocks3SaddleAReal 0 ≤ x := by
      simp [blocks3SaddleAReal, hx]
    have hright : x ≤ blocks3SaddleAReal x := by
      unfold blocks3SaddleAReal
      have hx0 : 0 ≤ x := hxpos.le
      nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) hx0]
    have hxI : x ∈ Set.Icc (blocks3SaddleAReal 0) (blocks3SaddleAReal x) :=
      ⟨hleft, hright⟩
    rcases intermediate_value_Icc hxpos.le hcont hxI with ⟨r, hrmem, hr⟩
    exact ⟨r, hrmem.1, hr⟩

/-- The nonnegative saddle radius solving `r+r^2+r^3/2=n`. -/
noncomputable def blocks3SaddleRadius (n : ℕ) : ℝ :=
  Classical.choose (blocks3SaddleAReal_exists_of_nonneg
    (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))

end Blocks3HAdmissible


