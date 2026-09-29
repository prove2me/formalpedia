-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR11.finite_approximations_of_exponentUpper
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:15:18.358185+00:00
-- url     : https://prove2.me/submissions/94a1afb4-eec8-4961-b396-b34308063e46

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_IrrationalityExponentR11
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_finite_bounded_denominator_approximations
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
theorem solution {ξ μ ν : ℝ}
    (h : ApproximationExponentUpper ξ μ) (hν : μ < ν) :
    (reducedApproximationPairs ξ ν).Finite := by
  obtain ⟨Q, _, hQ⟩ := h ν hν
  refine (finite_bounded_denominator_approximations ξ ν Q).subset ?_
  intro r hr
  refine ⟨hr, ?_⟩
  by_contra hnot
  have hQr : Q ≤ r.2 := Nat.le_of_not_gt hnot
  exact (not_lt_of_ge (hQ r.2 hQr r.1)) hr.2.2
