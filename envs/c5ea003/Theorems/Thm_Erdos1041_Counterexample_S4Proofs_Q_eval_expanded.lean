-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S4Proofs_Q_eval_expanded
-- name    : Erdos1041.Counterexample.S4Proofs.Q_eval_expanded
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:07:57.324288+00:00
-- url     : https://prove2.me/theorems/7dd5e0a7-c7cd-431c-a58b-28110a7024a9
-- title:
--   The model polynomial has the exact seven-term expansion
-- statement:
--   For every complex w, Q(w)=w⁷+a·w³+b·w²+c·w−s²·conj(a)·w⁴−s⁶·conj(b)·w⁵−s¹⁰·conj(c)·w⁶.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceCritical.lean#L388-L397
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
noncomputable section
open scoped ComplexConjugate NNReal
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Erdos1041.Counterexample.S4Proofs

theorem Erdos1041.Counterexample.S4Proofs.Q_eval_expanded (w : ℂ) :
    Q.eval w = w ^ 7 + a * w ^ 3 + b * w ^ 2 + c * w
      - (s : ℂ) ^ 2 * conj a * w ^ 4
      - (s : ℂ) ^ 6 * conj b * w ^ 5
      - (s : ℂ) ^ 10 * conj c * w ^ 6 := by sorry
