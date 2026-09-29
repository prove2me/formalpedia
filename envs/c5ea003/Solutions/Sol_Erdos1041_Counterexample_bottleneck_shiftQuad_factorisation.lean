-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_shiftQuad_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:28:04.796287+00:00
-- url     : https://prove2.me/submissions/5d0fd8ba-db4a-47ec-84bd-9de9f6a5a9c8

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
theorem solution (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) :
    p.comp (Polynomial.X + Polynomial.C cc) - Polynomial.C (p.eval cc) =
      Polynomial.X ^ 2 * shiftQuad p cc := by
  let q : Polynomial ℂ :=
    p.comp (Polynomial.X + Polynomial.C cc) - Polynomial.C (p.eval cc)
  have hq0 : q.coeff 0 = 0 := by
    simp [q, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  have hqd : (Polynomial.derivative q).eval 0 = 0 := by
    have hc : (Polynomial.derivative p).eval cc = 0 := hcrit
    simpa [q, Polynomial.derivative_comp, Polynomial.derivative_X_add_C,
      Polynomial.eval_comp] using hc
  have hq1 : q.coeff 1 = 0 := by
    have hdc : (Polynomial.derivative q).coeff 0 = 0 := by
      simpa only [Polynomial.coeff_zero_eq_eval_zero] using hqd
    simpa [Polynomial.coeff_derivative] using hdc
  have hdiv : (Polynomial.X : Polynomial ℂ) ^ 2 ∣ q := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro d hd
    have hd' : d = 0 ∨ d = 1 := by omega
    rcases hd' with rfl | rfl
    · exact hq0
    · exact hq1
  have hmod : q %ₘ (Polynomial.X ^ 2) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X.pow 2)).mpr hdiv
  have hidentity := Polynomial.modByMonic_add_div q (Polynomial.X ^ 2)
  rw [hmod, zero_add] at hidentity
  change q = Polynomial.X ^ 2 * (q /ₘ (Polynomial.X ^ 2))
  exact hidentity.symm
