-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bell
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_Bell
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:12:09.063153+00:00
-- url     : https://prove2.me/theorems/539a8810-4211-41b9-bb61-3227a45fdc19
-- title:
--   Bell decorated-partition coefficients and analytic series
-- statement:
--   The real coefficient B_n/n! uses the actual posInt.set counting class; its complex formal carrier maps the corresponding EGF. The analytic function is exp(exp(z)-1), with a composed formal multilinear exponential series and a nonnegative coefficient representation.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/Bell.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bound
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
import Mathlib
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch2 §II.1 — Labelled structures and exponential generating functions

Flajolet & Sedgewick, Part A, Chapter II. A *labelled* class is again a graded
family of finite types (we reuse `CombClass`), but is enumerated by its
*exponential* generating function (EGF)

  `A(z) = ∑ₙ Aₙ zⁿ/n!`.

This file defines the EGF and two foundational flagships:
- permutations (`Perm (Fin n)`, `Aₙ = n!`) with EGF `1/(1 - z)`;
- the "set" class (one object of each size) with EGF `e^z`.

The labelled product (the defining feature of EGFs) is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma coeff_egfSeq (a : ℕ → ℕ) (n : ℕ) :
    coeff n (egfSeq a) = (a n : ℚ) / (n.factorial : ℚ) := by
  rw [egfSeq, coeff_mk]

@[simp] lemma CombClass.coeff_egf (C : CombClass) (n : ℕ) :
    coeff n C.egf = (C.counts n : ℚ) / (n.factorial : ℚ) := by
  rw [CombClass.egf, coeff_egfSeq]

end AnalyticCombinatorics.Ch1

open Filter ENNReal
open scoped PowerSeries Topology NNReal ENNReal

noncomputable section

namespace PowerSeries

@[simp] lemma coeff_mapℂ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (mapℂ f) =
      algebraMap ℚ ℂ (PowerSeries.coeff (R := ℚ) n f) := by
  simp [mapℂ]

end PowerSeries
end



open Complex
open scoped NNReal ENNReal

noncomputable section

abbrev bellCoeffR (n : ℕ) : ℝ :=
  (AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) / n.factorial

lemma bellCoeffR_nonneg (n : ℕ) : 0 ≤ bellCoeffR n := by
  positivity

def bellCarrier : PowerSeries ℂ :=
  PowerSeries.mapℂ AnalyticCombinatorics.Ch1.CombClass.posInt.set.egf

@[simp] theorem bellCarrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n bellCarrier = (bellCoeffR n : ℂ) := by
  simp [bellCarrier, bellCoeffR, AnalyticCombinatorics.Ch1.CombClass.coeff_egf]

def bellCarrier_nonneg : NonnegRealCoeff bellCarrier where
  coeffR := bellCoeffR
  coeff_nonneg := bellCoeffR_nonneg
  coeff_eq := bellCarrier_coeff

noncomputable abbrev analyticBellFun (z : ℂ) : ℂ :=
  Complex.exp (Complex.exp z - 1)

noncomputable abbrev expSeriesC : FormalMultilinearSeries ℂ ℂ ℂ :=
  NormedSpace.expSeries ℂ ℂ

noncomputable abbrev analyticBellSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  expSeriesC.comp (expSeriesC - constFormalMultilinearSeries ℂ ℂ (1 : ℂ))

lemma exp_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.exp expSeriesC (0 : ℂ) := by
  have hsum : HasFPowerSeriesAt expSeriesC.sum expSeriesC (0 : ℂ) := by
    exact (expSeriesC.hasFPowerSeriesOnBall
      (by
        rw [expSeriesC, NormedSpace.expSeries_radius_eq_top]
        exact WithTop.top_pos)).hasFPowerSeriesAt
  have hfun : expSeriesC.sum = Complex.exp := by
    funext z
    calc
      expSeriesC.sum z = NormedSpace.exp z := by
        exact congrFun (NormedSpace.exp_eq_expSeries_sum ℂ).symm z
      _ = Complex.exp z := by
        exact (congrFun Complex.exp_eq_exp_ℂ z).symm
  rwa [hfun] at hsum

lemma exp_sub_one_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => Complex.exp z - 1)
      (expSeriesC - constFormalMultilinearSeries ℂ ℂ (1 : ℂ)) (0 : ℂ) := by
  simpa using
    (exp_hasFPowerSeriesAt_zero.sub
      (hasFPowerSeriesAt_const (𝕜 := ℂ) (e := (0 : ℂ)) (c := (1 : ℂ))))

lemma analyticBell_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt analyticBellFun analyticBellSeries (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp expSeriesC
      ((fun z : ℂ => Complex.exp z - 1) 0) := by
    simpa using exp_hasFPowerSeriesAt_zero
  have h := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := fun z : ℂ => Complex.exp z - 1)
    houter exp_sub_one_hasFPowerSeriesAt_zero
  simpa [Function.comp_def, analyticBellFun, analyticBellSeries] using h


