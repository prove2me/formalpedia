-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR11.irrationalityExponent_le_of_exponentUpper
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:17:07.127983+00:00
-- url     : https://prove2.me/submissions/c896b40b-835e-4a47-9459-cc38c273bdcc

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_IrrationalityExponentR11
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_finite_approximations_of_exponentUpper
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_neg_one_mem_approximationExponents
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

















lemma approximationExponents_nonempty (ξ : ℝ) :
    (approximationExponents ξ).Nonempty :=
  ⟨-1, neg_one_mem_approximationExponents ξ⟩
end ErdosProblems.Erdos1049.PaperR11

open Filter Set
open scoped BigOperators Topology
open PaperR9 PaperR10
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR10 in
open ErdosProblems.Erdos1049.PaperR9 in
theorem solution {ξ μ : ℝ}
    (h : ApproximationExponentUpper ξ μ) :
    irrationalityExponent ξ ≤ μ := by
  apply csSup_le (approximationExponents_nonempty ξ)
  intro ν hν
  apply le_of_not_gt
  intro hgt
  exact hν (finite_approximations_of_exponentUpper h hgt)
