-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneckSlitDomain_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:32:59.140991+00:00
-- url     : https://prove2.me/submissions/b995f084-fba5-4dde-a8cc-7e7edbde649c

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlitBase_isOpen
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

namespace Erdos1041.Counterexample
/-- The slit-complement domain is exactly the part of that preimage lying in the
distinguished component. -/
theorem bottleneckSlitDomain_eq (p : Polynomial ℂ) (cc : ℂ) :
    bottleneckSlitDomain p cc =
      connectedComponentIn (Omega p) cc ∩
        (fun z => p.eval z) ⁻¹' bottleneckSlitBase (p.eval cc) := by
  ext z
  constructor
  · rintro ⟨hU, hJ⟩
    exact ⟨hU, connectedComponentIn_subset (Omega p) cc hU, hJ⟩
  · rintro ⟨hU, -, hJ⟩
    exact ⟨hU, hJ⟩
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (p : Polynomial ℂ) (cc : ℂ)
    (hv : p.eval cc ≠ 0) : IsOpen (bottleneckSlitDomain p cc) := by
  have hOopen : IsOpen (Omega p) :=
    isOpen_lt p.continuous.norm continuous_const
  rw [bottleneckSlitDomain_eq]
  exact hOopen.connectedComponentIn.inter
    ((bottleneckSlitBase_isOpen (p.eval cc) hv).preimage p.continuous)
