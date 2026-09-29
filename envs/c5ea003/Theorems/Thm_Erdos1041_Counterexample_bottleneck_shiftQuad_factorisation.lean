-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneck_shiftQuad_factorisation
-- name    : Erdos1041.Counterexample.bottleneck_shiftQuad_factorisation
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:27:10.213981+00:00
-- url     : https://prove2.me/theorems/b52a81f7-c0a9-418d-8781-94a458b5427a
-- title:
--   A critical point gives a quadratic factor
-- statement:
--   If cc is a root of the derivative of p, then p(cc+X)−p(cc)=X² shiftQuad(p,cc).
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L105-L134
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

open Erdos1041
open Erdos1041.Counterexample
noncomputable section
open Topology

open Erdos1041.Counterexample

theorem Erdos1041.Counterexample.bottleneck_shiftQuad_factorisation (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) :
    p.comp (Polynomial.X + Polynomial.C cc) - Polynomial.C (p.eval cc) =
      Polynomial.X ^ 2 * shiftQuad p cc := by sorry
