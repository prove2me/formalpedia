-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_neg_one_mem_approximationExponents
-- name    : ErdosProblems.Erdos1049.PaperR11.neg_one_mem_approximationExponents
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:05:55.894878+00:00
-- url     : https://prove2.me/theorems/09322bac-2112-4005-9c74-1e3ce1d3016f
-- title:
--   Neg one mem approximation exponents
-- statement:
--   For every real ξ, −1 belongs to the source-defined set approximationExponents(ξ), including when ξ is rational.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/IrrationalityExponentR11.lean#L88-L116
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

theorem ErdosProblems.Erdos1049.PaperR11.neg_one_mem_approximationExponents (ξ : ℝ) :
    (-1 : ℝ) ∈ approximationExponents ξ := by sorry
