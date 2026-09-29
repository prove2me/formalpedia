-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR11.neg_one_mem_approximationExponents
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:13:48.935193+00:00
-- url     : https://prove2.me/submissions/4bcc583c-8eb4-452b-a2ff-72f4acca177a

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_IrrationalityExponentR11
import Theorems.Thm_ErdosProblems_Erdos1049_BezoutPluckerJets_bezoutPluckerEquiv_apply
import Lean.Elab.Tactic.Omega
import Mathlib
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

namespace PaperR10
end PaperR10

namespace PaperR9
end PaperR9

/-!
# The supremum definition of the irrationality exponent

Bounds the supremum exponent, real and extended, from quadratic linear forms.
Denominators are positive naturals and numerators are arbitrary integers.
Finiteness of the numerators at bounded denominators is proved, not assumed.
The extended-real definition also covers an unbounded exponent set.
-/

namespace ErdosProblems.Erdos1049.PaperR11
open Filter Set
open scoped BigOperators Topology
open PaperR9 PaperR10
end ErdosProblems.Erdos1049.PaperR11

open Filter Set
open scoped BigOperators Topology
open PaperR9 PaperR10
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR10 in
open ErdosProblems.Erdos1049.PaperR9 in
theorem solution (ξ : ℝ) :
    (-1 : ℝ) ∈ approximationExponents ξ := by
  classical
  change (reducedApproximationPairs ξ (-1)).Infinite
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (|ξ| + 1)
  let q : ℕ := max (B + 1) (N + 1)
  have hqB : B < q := (Nat.lt_succ_self B).trans_le (le_max_left _ _)
  have hqN : N < q := (Nat.lt_succ_self N).trans_le (le_max_right _ _)
  have hq : 0 < q := (Nat.zero_le B).trans_lt hqB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.succ_le_iff.mpr hq : 1 ≤ q)
  have hinv : |(1 : ℝ) / (q : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (q : ℝ))]
    exact (div_le_iff₀ hqR).mpr (by simpa using hq1)
  have happ : |ξ - (1 : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-(-1 : ℝ)) := by
    calc
      |ξ - (1 : ℝ) / (q : ℝ)| ≤ |ξ| + |(1 : ℝ) / (q : ℝ)| := abs_sub _ _
      _ ≤ |ξ| + 1 := by linarith
      _ < (N : ℝ) := hN
      _ < (q : ℝ) := by exact_mod_cast hqN
      _ = (q : ℝ) ^ (-(-1 : ℝ)) := by norm_num
  have hmem : ((1 : ℤ), q) ∈ reducedApproximationPairs ξ (-1) := by
    exact ⟨hq, by simp, by simpa using happ⟩
  have hqle : q ≤ B := hB ⟨((1 : ℤ), q), hmem, rfl⟩
  exact (not_lt_of_ge hqle) hqB
