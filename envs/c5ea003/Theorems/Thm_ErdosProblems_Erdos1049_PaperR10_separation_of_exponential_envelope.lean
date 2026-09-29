-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR10_separation_of_exponential_envelope
-- name    : ErdosProblems.Erdos1049.PaperR10.separation_of_exponential_envelope
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:13:53.804153+00:00
-- url     : https://prove2.me/theorems/2d2bef18-92b8-40a9-b000-b9c222c23abc
-- title:
--   Separation of exponential envelope
-- statement:
--   Let A,B,p be integers, q a positive natural number, and ξ,u,v,w real. If exp(−u)≤|Aξ−B|≤exp(−v), |A|≤exp(w), and log(2q)≤v, then |ξ−p/q|≥exp(−(u+w)).
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/QuadraticMeasureR10.lean#L25-L54
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_QuadraticMeasureR10
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
open Filter
open scoped Topology
open PaperR9

open ErdosProblems.Erdos1049.PaperR10

open ErdosProblems.Erdos1049.PaperR9

theorem ErdosProblems.Erdos1049.PaperR10.separation_of_exponential_envelope
    (A B p : ℤ) (q : ℕ) (ξ u v w : ℝ) (hq : 0 < q)
    (hlo : Real.exp (-u) ≤ |(A : ℝ) * ξ - B|)
    (hup : |(A : ℝ) * ξ - B| ≤ Real.exp (-v))
    (hA : |(A : ℝ)| ≤ Real.exp w)
    (hcross : Real.log (2 * (q : ℝ)) ≤ v) :
    Real.exp (-(u + w)) ≤ |ξ - (p : ℝ) / (q : ℝ)| := by sorry
