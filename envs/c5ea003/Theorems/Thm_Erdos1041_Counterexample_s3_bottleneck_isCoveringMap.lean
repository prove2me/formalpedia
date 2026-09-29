-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_s3_bottleneck_isCoveringMap
-- name    : Erdos1041.Counterexample.s3_bottleneck_isCoveringMap
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:31:51.402685+00:00
-- url     : https://prove2.me/theorems/47301b17-6a79-4b16-97b9-3c3f9fb9cd7a
-- title:
--   The polynomial slit projection is a covering map
-- statement:
--   For positive-degree p, if cc is in the strict lemniscate, p(cc) is nonzero, and cc is the only critical point in that component, polynomial evaluation on the slit domain is a covering of the slit base.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L1056-L1065
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

theorem Erdos1041.Counterexample.s3_bottleneck_isCoveringMap (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p) (hv : p.eval cc ≠ 0) (hdeg : 0 < p.natDegree)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc) :
    IsCoveringMap (bottleneckSlitProjection p cc) := by sorry
