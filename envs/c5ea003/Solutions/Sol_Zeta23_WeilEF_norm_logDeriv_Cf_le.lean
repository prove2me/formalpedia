-- Prove2me | solution 1 for Zeta23.WeilEF.norm_logDeriv_Cf_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:39:43.982527+00:00
-- url     : https://prove2.me/submissions/d089ab27-fb26-4b8b-ac51-8480154a4391

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Theorems.Thm_AnalyticOn_norm_le_of_norm_le_on_sphere
import Theorems.Thm_CfAnalytic
import Theorems.Thm_LogOfAnalyticFunction
import Theorems.Thm_ZerosBound
import Theorems.Thm_Zeta23_WeilEF_Cf_ne_zero

-- from Zeta23.FromPNTPlus.StrongPNTPrefix
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/StrongPNT.lean (sorry-free prefix, truncated before JBlaschke/ZeroInequality).
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: kept only a prefix of the file (through `ZerosBound`: the Blaschke-factor /
Borel–Carathéodory bound on zeros in a disk; the remainder of StrongPNT.lean is not ported),
removed the Architect blueprint tooling (import Architect, blueprint_comment blocks,
@[blueprint ...] attributes), dropped the intra-project import of MediumPNT together with the
local notations and the `open ArithmeticFunction` that only the unported remainder used (the two Mathlib
imports previously reached through MediumPNT are imported directly), and added
`import Zeta23.Prelude.InstancePriorities` (this project's instance-priority settings).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory


theorem borelCaratheodory' {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (hyp_r : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have h_borelCaratheodory : ∀ ε > 0, ‖f z‖ ≤ (2 * (M + ε) * ‖z‖) / (R - ‖z‖) := by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith, analytic.differentiableOn, fun z hz => by rw [Set.mem_setOf_eq]; linarith [realPartBounded z hz], Rpos, by exact Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp hyp_z ) hyp_r ), zeroAtZero]
  have h_limit : ‖f z‖ ≤ (2 * M * ‖z‖) / (R - ‖z‖) := by
    have h_limit : Filter.Tendsto (fun ε => (2 * (M + ε) * ‖z‖) / (R - ‖z‖)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * M * ‖z‖) / (R - ‖z‖))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const).div_const _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_borelCaratheodory ε hε );
  rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
  refine le_trans h_limit ?_;
  gcongr
  · exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) hyp_z)

lemma cauchy_formula_deriv {r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (hf_on_ball : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  have hz_in_ball : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt r_lt_r'
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball r'_lt_R) hf_on_ball hz_in_ball]

lemma DerivativeBound {M r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (pos_r : 0 < r) (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (z_in_r : z ∈ Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [cauchy_formula_deriv r_lt_r' r'_lt_R analytic_f.differentiableOn  z_in_r, one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith) (C := 2 * M * r' / ((R - r') * (r' - r) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[borelCaratheodory' Mpos (by grind) r'_lt_R analytic_f f_zero_at_zero  re_f_le_M
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r' - r) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist : r' - r ≤ ‖z' - z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
        _root_.dist_zero_right] at hz' z_in_r
      rw [← hz']
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr

theorem BorelCaratheodoryDeriv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (rpos : 0 < r) (hyp_r : r < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  have hr' : 2 * M * ((R + r) / 2) ^ 2 / ((R - (R + r) / 2) * ((R + r) / 2 - r) ^ 2) =
      4 * M * (R + r) ^ 2 / (R - r) ^ 3 := by field_simp; ring
  calc ‖deriv f z‖
      _ ≤ 4 * M * (R + r) ^ 2 / (R - r) ^ 3 := hr' ▸
          DerivativeBound Mpos rpos (by linarith) (by linarith) analytic_f zeroAtZero realPartBounded hyp_z
      _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
          have : 16 * M * R ^ 2 = 4 * M * (2 * R) ^ 2 := by ring_nf
          rw [this]; bound





open Classical












end

-- from Zeta23.WeilEF.Landau
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Landau.lean

Landau's lemma (Borel–Carathéodory + Jensen route; Mathlib: Analysis/Complex/BorelCaratheodory,
JensenFormula): zero counts and the partial-fraction expansion of f'/f on disks, specialized to ζ.
`zeta_local_zero_count` is consumed downstream as `RiemannVonMangoldt.local_count`.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set


section UnitDisk

open Metric










end UnitDisk



end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex Set
open Metric

theorem solution {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hfin : (SetOfZeros 1 f).Finite) (hB2 : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83/100) :
    ‖logDeriv (Cf (22/25) f) z‖ ≤ 44795000 * Real.log B := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hfinr : (SetOfZeros (22/25) f).Finite := finiteSetOfZeros_mono (by norm_num) hfin
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  -- total multiplicity bound (ZerosBound with r = 22/25, R = 24/25)
  have hcount : ((∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset,
      analyticOrderNatAt f ρ : ℕ) : ℝ) ≤ 1 / Real.log ((24/25) / (22/25)) * Real.log B := by
    exact_mod_cast ZerosBound (by norm_num) (by norm_num)
      (by norm_num : (22/25:ℝ) < 24/25) (by norm_num) hfa hf0 hfin (fun w hw => hfB w hw)
  set K : ℕ := ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset,
    analyticOrderNatAt f ρ with hK
  -- Cf on the sphere of radius 24/25
  have hsphere : ∀ w : ℂ, ‖w‖ = 24/25 → ‖Cf (22/25) f w‖ ≤ B * (25/2 : ℝ) ^ K := by
    intro w hw
    have hwmem : w ∉ SetOfZeros (22/25) f := by
      intro h
      have := h.1
      rw [hw] at this
      norm_num at this
    have hfinr34 := finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin
    have hdist : ∀ ρ ∈ hfinr34.toFinset, (2/25 : ℝ) ≤ ‖w - ρ‖ := by
      intro ρ hρ
      have hρ' := hfinr34.mem_toFinset.mp hρ
      calc (2/25 : ℝ) = 24/25 - 22/25 := by norm_num
        _ ≤ ‖w‖ - ‖ρ‖ := by
            have := hρ'.1
            rw [hw]
            linarith
        _ ≤ ‖w - ρ‖ := norm_sub_norm_le w ρ
    have hprod_lb : ((2/25 : ℝ)) ^ K ≤ ‖∏ ρ ∈ hfinr34.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ := by
      rw [norm_prod, hK, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      rw [norm_pow]
      exact pow_le_pow_left₀ (by norm_num) (hdist ρ hρ) _
    unfold Cf
    rw [dif_pos hfinr34, dif_neg hwmem]
    rw [norm_div]
    have hprod_pos : (0:ℝ) < ‖∏ ρ ∈ hfinr34.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ :=
      lt_of_lt_of_le (by positivity) hprod_lb
    rw [div_le_iff₀ hprod_pos]
    calc ‖f w‖ ≤ B := hfB w (le_of_eq hw)
      _ = B * (25/2 : ℝ) ^ K * (2/25 : ℝ) ^ K := by
          rw [mul_assoc, ← mul_pow]
          norm_num
      _ ≤ B * (25/2 : ℝ) ^ K * ‖∏ ρ ∈ hfinr34.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ := by
          have hB0 : (0:ℝ) ≤ B * (25/2 : ℝ) ^ K := by positivity
          exact mul_le_mul_of_nonneg_left hprod_lb hB0
  -- inside by the maximum principle
  have hball : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖Cf (22/25) f w‖ ≤ B * (25/2 : ℝ) ^ K := by
    intro w hw
    have hCfa : AnalyticOn ℂ (Cf (22/25) f) (Metric.closedBall 0 (24/25)) :=
      ((CfAnalytic (by norm_num : (22/25:ℝ) < 39/40) (by norm_num) hfa hf0').mono
        (Metric.closedBall_subset_closedBall (by norm_num))).analyticOn
    refine AnalyticOn.norm_le_of_norm_le_on_sphere le_rfl hCfa (fun v hv => ?_)
      (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero])
    refine hsphere v ?_
    rw [mem_sphere_iff_norm, sub_zero] at hv
    exact hv
  -- lower bound at the centre
  have hCf0 : (1:ℝ) ≤ ‖Cf (22/25) f 0‖ := by
    have h0mem : (0:ℂ) ∉ SetOfZeros (22/25) f := fun h => hf0' h.2
    have hfinr34 := finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin
    unfold Cf
    rw [dif_pos hfinr34, dif_neg h0mem, norm_div, hf0, norm_one]
    rw [le_div_iff₀]
    · rw [one_mul, norm_prod]
      refine Finset.prod_le_one (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      have hρ' := hfinr34.mem_toFinset.mp hρ
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      rw [zero_sub, norm_neg]
      linarith [hρ'.1]
    · rw [norm_prod]
      refine Finset.prod_pos (fun ρ hρ => ?_)
      have hρ' := hfinr34.mem_toFinset.mp hρ
      have hρ0 : ρ ≠ 0 := by
        rintro rfl
        exact hf0' hρ'.2
      rw [norm_pow, zero_sub, norm_neg]
      exact pow_pos (norm_pos_iff.mpr hρ0) _
  -- the analytic logarithm and Borel–Carathéodory
  obtain ⟨J, hJa, hJ0, hJd, hJre⟩ := LogOfAnalyticFunction
    (by norm_num : (0:ℝ) < 17/20) (by norm_num : (17/20:ℝ) < 22/25)
    ((CfAnalytic (by norm_num : (22/25:ℝ) < 9/10) (by norm_num) hfa hf0').mono
      (Metric.closedBall_subset_closedBall (by norm_num)))
    (fun v hv => Cf_ne_zero hfa hf0' (by norm_num) hfin
      (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hv))
  set M' : ℝ := (1 + Real.log (25/2) / Real.log ((24/25) / (22/25))) * Real.log B with hM'
  have hlog76 : (0:ℝ) < Real.log ((24/25) / (22/25)) := Real.log_pos (by norm_num)
  have hM'pos : 0 < M' := by
    rw [hM']
    have : (0:ℝ) < 1 + Real.log (25/2) / Real.log ((24/25) / (22/25)) := by positivity
    positivity
  have hre : ∀ v ∈ Metric.closedBall (0:ℂ) (17/20), (J v).re ≤ M' := by
    intro v hv
    rw [← (hJre v (Metric.closedBall_subset_ball (by norm_num) hv))]
    have hv' : ‖v‖ ≤ 24/25 := by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hv
      linarith
    have h1 : Real.log ‖Cf (22/25) f v‖ ≤ Real.log (B * (25/2 : ℝ) ^ K) := by
      rcases eq_or_ne (Cf (22/25) f v) 0 with h | h
      · rw [h, norm_zero, Real.log_zero]
        refine Real.log_nonneg ?_
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ B * (25/2 : ℝ) ^ K := by
              refine mul_le_mul (by linarith) (one_le_pow₀ (by norm_num)) (by norm_num)
                (by linarith)
      · exact Real.log_le_log (norm_pos_iff.mpr h) (hball v hv')
    have h2 : (0:ℝ) ≤ Real.log ‖Cf (22/25) f 0‖ := Real.log_nonneg hCf0
    have h3 : Real.log (B * (25/2 : ℝ) ^ K) = Real.log B + K * Real.log (25/2) := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    have h4 : (K : ℝ) * Real.log (25/2) ≤ (Real.log B / Real.log ((24/25)/(22/25))) * Real.log (25/2) := by
      have hlog8 : (0:ℝ) ≤ Real.log (25/2) := Real.log_nonneg (by norm_num)
      have hKle : (K:ℝ) ≤ Real.log B / Real.log ((24/25)/(22/25)) := by
        rw [div_eq_inv_mul, ← one_div]
        exact hcount
      exact mul_le_mul_of_nonneg_right hKle hlog8
    have h5 : Real.log ‖Cf (22/25) f v‖ - Real.log ‖Cf (22/25) f 0‖
        ≤ Real.log B + (K:ℝ) * Real.log (25/2) := by
      rw [← h3]
      linarith
    rw [hM']
    calc Real.log ‖Cf (22/25) f v‖ - Real.log ‖Cf (22/25) f 0‖
        ≤ Real.log B + (K:ℝ) * Real.log (25/2) := h5
      _ ≤ Real.log B + (Real.log B / Real.log ((24/25)/(22/25))) * Real.log (25/2) := by linarith
      _ = (1 + Real.log (25/2) / Real.log ((24/25) / (22/25))) * Real.log B := by
          field_simp
  have hbc := BorelCaratheodoryDeriv hM'pos (by norm_num : (0:ℝ) < 83/100)
    (by norm_num : (83/100:ℝ) < 17/20)
    ((hJa.mono (Metric.ball_subset_ball (by norm_num))).analyticOn) hJ0
    (fun v hv => hre v (Metric.ball_subset_closedBall hv))
    (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero])
  have hzmem : z ∈ Metric.closedBall (0:ℂ) (17/20) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    linarith
  have hderivJ : deriv J z = logDeriv (Cf (22/25) f) z := by
    rw [hJd z (by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
      linarith), logDeriv]
    rfl
  rw [← hderivJ]
  refine hbc.trans ?_
  -- 16 * M' * (17/20)^2 / (17/20 - 83/100)^3 = 1445000 * M' ≤ 1445000 * 31 * log B
  have hM'le : M' ≤ 31 * Real.log B := by
    rw [hM']
    have h8 : Real.log (25/2) ≤ 30 * Real.log ((24/25) / (22/25)) := by
      have h714 : (25/2:ℝ) ≤ ((24/25)/(22/25)) ^ (30:ℕ) := by norm_num
      calc Real.log (25/2) ≤ Real.log (((24/25)/(22/25)) ^ (30:ℕ)) :=
            Real.log_le_log (by norm_num) h714
        _ = 30 * Real.log ((24/25)/(22/25)) := by rw [Real.log_pow]; push_cast; ring
    have hcoef : 1 + Real.log (25/2) / Real.log ((24/25) / (22/25)) ≤ 31 := by
      have hd : Real.log (25/2) / Real.log ((24/25)/(22/25)) ≤ 30 :=
        (div_le_iff₀ hlog76).mpr (by linarith)
      linarith
    exact mul_le_mul_of_nonneg_right hcoef hlogB.le
  calc 16 * M' * (17/20:ℝ) ^ 2 / ((17/20:ℝ) - 83/100) ^ 3 = 1445000 * M' := by
        field_simp
        ring
    _ ≤ 1445000 * (31 * Real.log B) := by
        exact mul_le_mul_of_nonneg_left hM'le (by norm_num)
    _ = 44795000 * Real.log B := by ring
