-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_IrrationalityExponentR11
-- name    : ErdosProblems_Erdos1049_IrrationalityExponentR11
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:47:08.445895+00:00
-- url     : https://prove2.me/theorems/47f329d8-cad7-454f-8cd7-d4fb5f278ef4
-- title:
--   The supremum definition of the irrationality exponent
-- statement:
--   Reduced rational approximation pairs define the real supremum exponent; bounded-denominator finiteness and the eventual quadratic-form separation bound control that supremum. The submitted module contains the source declarations reducedApproximationPairs, approximationExponents, irrationalityExponent, extendedIrrationalityExponent, approximation_numerator_bound, among others. Source topic: The supremum definition of the irrationality exponent.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/IrrationalityExponentR11.lean#L17-L175
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
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

/-- Reduced rational pairs satisfying the paper's strict inequality. -/
def reducedApproximationPairs (ξ ν : ℝ) : Set (ℤ × ℕ) :=
  {r | 0 < r.2 ∧ Nat.Coprime r.1.natAbs r.2 ∧
    |ξ - (r.1 : ℝ) / (r.2 : ℝ)| < (r.2 : ℝ) ^ (-ν)}

def approximationExponents (ξ : ℝ) : Set ℝ :=
  {ν | (reducedApproximationPairs ξ ν).Infinite}

/-- Used with a proved upper bound; the extended definition is used otherwise. -/
noncomputable def irrationalityExponent (ξ : ℝ) : ℝ :=
  sSup (approximationExponents ξ)























end ErdosProblems.Erdos1049.PaperR11


