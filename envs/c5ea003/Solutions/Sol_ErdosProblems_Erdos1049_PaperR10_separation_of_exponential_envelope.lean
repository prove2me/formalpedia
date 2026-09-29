-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.separation_of_exponential_envelope
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:15:19.060536+00:00
-- url     : https://prove2.me/submissions/8c2386c8-0305-4c7c-8e81-77e5bce4cdac

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Theorems.Thm_ErdosProblems_Erdos1049_rational_separation_of_small_integer_form
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.ZetaValues
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace PaperR9
end PaperR9

/-!
# A complete quadratic-mesh irrationality-measure consumer

The conclusion is uniform over all integer numerators
and all sufficiently large positive denominators. No independence assumption
on successive coefficient pairs is used. The actual 2004 source construction
is NOT asserted by this module.
-/

namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped Topology
open PaperR9
end ErdosProblems.Erdos1049.PaperR10

open Filter
open scoped Topology
open PaperR9
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
open ErdosProblems.Erdos1049.PaperR9 in
theorem solution
    (A B p : ℤ) (q : ℕ) (ξ u v w : ℝ) (hq : 0 < q)
    (hlo : Real.exp (-u) ≤ |(A : ℝ) * ξ - B|)
    (hup : |(A : ℝ) * ξ - B| ≤ Real.exp (-v))
    (hA : |(A : ℝ)| ≤ Real.exp w)
    (hcross : Real.log (2 * (q : ℝ)) ≤ v) :
    Real.exp (-(u + w)) ≤ |ξ - (p : ℝ) / (q : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h2q : (0 : ℝ) < 2 * q := by positivity
  have hsmall : 2 * (q : ℝ) * |(A : ℝ) * ξ - B| ≤ 1 := by
    calc
      2 * (q : ℝ) * |(A : ℝ) * ξ - B| ≤
          2 * (q : ℝ) * Real.exp (-v) :=
        mul_le_mul_of_nonneg_left hup h2q.le
      _ ≤ 2 * (q : ℝ) * Real.exp (-Real.log (2 * (q : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ h2q.le
        exact Real.exp_le_exp.mpr (neg_le_neg hcross)
      _ = 1 := by rw [Real.exp_neg, Real.exp_log h2q, mul_inv_cancel₀ h2q.ne']
  have hsep := rational_separation_of_small_integer_form A B p (q : ℤ) ξ
    (by exact_mod_cast hq) (by simpa using hsmall)
  have hsep' : |(A : ℝ) * ξ - B| ≤
      |(A : ℝ)| * |ξ - (p : ℝ) / (q : ℝ)| := by
    simpa using hsep
  have hmain : Real.exp (-u) ≤ Real.exp w * |ξ - (p : ℝ) / (q : ℝ)| := by
    exact hlo.trans (hsep'.trans
      (mul_le_mul_of_nonneg_right hA (abs_nonneg _)))
  have hdivide : Real.exp (-u) / Real.exp w ≤ |ξ - (p : ℝ) / (q : ℝ)| :=
    (div_le_iff₀ (Real.exp_pos w)).mpr (by simpa [mul_comm] using hmain)
  simpa only [← Real.exp_sub, show -u - w = -(u + w) by ring] using hdivide
