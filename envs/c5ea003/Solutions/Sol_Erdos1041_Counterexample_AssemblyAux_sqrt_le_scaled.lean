-- Prove2me | solution 1 for Erdos1041.Counterexample.AssemblyAux.sqrt_le_scaled
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:18:11.523837+00:00
-- url     : https://prove2.me/submissions/bc5c8b66-c247-481a-a35c-ba3ea8821aeb

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

namespace Erdos1041.Counterexample.AssemblyAux
end Erdos1041.Counterexample.AssemblyAux

noncomputable section
open scoped ComplexConjugate ENNReal

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.AssemblyAux
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.AssemblyAux in
theorem solution {r e δ M : ℝ} (hr : 0 < r) (he : 0 < e)
    (hδ : δ ≤ r ^ 7 * e ^ 7 * (36 / 5 / 10 ^ 6))
    (hM : 180 * r ^ 5 * e ^ 5 ≤ M) :
    Real.sqrt (δ / M) ≤ r * e / 5000 := by
  have hcoeff : 0 < (180 : ℝ) * r ^ 5 * e ^ 5 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hr 5)) (pow_pos he 5)
  have hMpos : 0 < M := lt_of_lt_of_le hcoeff hM
  have hmul : δ ≤ (r * e / 5000) ^ 2 * M := calc
    δ ≤ r ^ 7 * e ^ 7 * (36 / 5 / 10 ^ 6) := hδ
    _ = (r * e / 5000) ^ 2 * (180 * r ^ 5 * e ^ 5) := by ring
    _ ≤ (r * e / 5000) ^ 2 * M :=
      mul_le_mul_of_nonneg_left hM (sq_nonneg _)
  have hdiv : δ / M ≤ (r * e / 5000) ^ 2 := (div_le_iff₀ hMpos).2 hmul
  have hnonneg : 0 ≤ r * e / 5000 :=
    le_of_lt (div_pos (mul_pos hr he) (by norm_num))
  calc
    Real.sqrt (δ / M) ≤ Real.sqrt ((r * e / 5000) ^ 2) :=
      Real.sqrt_le_sqrt hdiv
    _ = r * e / 5000 := Real.sqrt_sq hnonneg
