-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_natDegree_pos
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:30:10.777248+00:00
-- url     : https://prove2.me/submissions/f935415f-62e8-4af4-b096-a0bc9019ef04

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

noncomputable section
open Topology

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (p : Polynomial ℂ) (cc b : ℂ)
    (hv : p.eval cc ≠ 0) (hr : p.IsRoot b) : 0 < p.natDegree := by
  by_contra hnot
  have hdeg : p.natDegree = 0 := by omega
  have hpC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have heq : p.eval cc = p.eval b := by
    rw [hpC]
    simp only [Polynomial.eval_C]
  exact hv (heq.trans hr)
