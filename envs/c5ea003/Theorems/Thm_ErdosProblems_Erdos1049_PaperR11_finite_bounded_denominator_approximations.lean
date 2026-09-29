-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_finite_bounded_denominator_approximations
-- name    : ErdosProblems.Erdos1049.PaperR11.finite_bounded_denominator_approximations
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:05:30.597837+00:00
-- url     : https://prove2.me/theorems/f20e41ec-076d-4648-a892-cc0a40e03fe6
-- title:
--   Finite bounded denominator approximations
-- statement:
--   For any real ξ,ν and natural Q, the reduced rational approximation pairs to ξ of exponent ν whose denominator is less than Q form a finite set.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/IrrationalityExponentR11.lean#L47-L74
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
import Definitions.Def_ErdosProblems_Erdos1049_IrrationalityExponentR11
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
open Filter Set
open scoped BigOperators Topology
open PaperR9 PaperR10

open ErdosProblems.Erdos1049.PaperR11

open ErdosProblems.Erdos1049.PaperR10
open ErdosProblems.Erdos1049.PaperR9

theorem ErdosProblems.Erdos1049.PaperR11.finite_bounded_denominator_approximations (ξ ν : ℝ) (Q : ℕ) :
    {r : ℤ × ℕ | r ∈ reducedApproximationPairs ξ ν ∧ r.2 < Q}.Finite := by sorry
