-- Prove2me | solution 1 for Blocks3HAdmissible.blocks3_count_over_factorial_isEquivalent_real_saddle
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T02:49:40.905865+00:00
-- url     : https://prove2.me/submissions/37e07d9a-a0c1-4a51-8bf2-365ba3cc04ae

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bound
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Exp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bell
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3RealSaddle
import Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_egf_set
import Mathlib
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
open Filter ENNReal
open scoped PowerSeries Topology NNReal ENNReal

noncomputable section

namespace PowerSeries

@[simp] lemma coeff_toFMLS (f : PowerSeries ℂ) (n : ℕ) :
    (toFMLS f).coeff n = PowerSeries.coeff (R := ℂ) n f := by
  simp [toFMLS]

@[simp] lemma nnnorm_toFMLS_apply (f : PowerSeries ℂ) (n : ℕ) :
    ‖toFMLS f n‖₊ = ‖PowerSeries.coeff (R := ℂ) n f‖₊ := by
  apply NNReal.eq
  simp [toFMLS]

end PowerSeries
end
end

section
open Complex
open scoped NNReal ENNReal

noncomputable section

theorem coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 R)) (n : ℕ) :
    p.coeff n =
      (2 * Real.pi * I : ℂ)⁻¹ •
        circleIntegral
          (fun z => ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z)
          0 R := by
  have hq : HasFPowerSeriesAt f (cauchyPowerSeries f 0 R) 0 := by
    have hnn : 0 < ((⟨R, hR.le⟩ : ℝ≥0)) := by
      exact_mod_cast hR
    exact (hd.hasFPowerSeriesOnBall hnn).hasFPowerSeriesAt
  have hpq : p = cauchyPowerSeries f 0 R := hp.eq_formalMultilinearSeries hq
  calc
    p.coeff n = (cauchyPowerSeries f 0 R).coeff n := by rw [hpq]
    _ = (cauchyPowerSeries f 0 R n fun _ => (1 : ℂ)) := by rfl
    _ = _ := by exact cauchyPowerSeries_apply f 0 R n 1

end
end

section
/-!
# Real-valued central-binomial and Catalan asymptotics

This file reflects the complex-valued asymptotic equivalents back to their
natural real-valued forms.
-/

open Filter Asymptotics
open scoped Topology BigOperators

lemma ofReal_isEquivalent_iff {f g : ℕ → ℝ} :
    ((fun n => (f n : ℂ)) ~[atTop] (fun n => (g n : ℂ))) ↔
      f ~[atTop] g := by
  constructor
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn
end

section
open scoped BigOperators PowerSeries
open List Finset

noncomputable section

namespace FormalMultilinearSeries

lemma ofScalars_comp_coeff (a b : ℕ → ℂ) (n : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ a).comp
      (FormalMultilinearSeries.ofScalars ℂ b)).coeff n =
      ∑ c : Composition n, a c.length * ∏ i : Fin c.length, b (c.blocksFun i) := by
  rw [FormalMultilinearSeries.coeff]
  simp [FormalMultilinearSeries.comp, FormalMultilinearSeries.applyComposition,
    FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn, smul_eq_mul]

end FormalMultilinearSeries

private lemma prod_coeff_eq_zero_of_not_pos {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0)
    {d n : ℕ} (l : { l : Fin d → ℕ // ∑ i, l i = n })
    (hl : ¬ ∀ i, 0 < l.1 i) :
    (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) = 0 := by
  classical
  push Not at hl
  rcases hl with ⟨i, hi⟩
  have hzero : l.1 i = 0 := Nat.eq_zero_of_le_zero hi
  rw [Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [hzero]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg

private lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero
    {g : ℂ⟦X⟧} (hg : PowerSeries.constantCoeff g = 0)
    {n d : ℕ} (hnd : n < d) :
    PowerSeries.coeff n (g ^ d) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    exact PowerSeries.coeff_of_lt_order n
      (lt_of_lt_of_le (by exact_mod_cast hnd)
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg))

private lemma coeff_pow_eq_sum_composition_length {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (d n : ℕ) :
    PowerSeries.coeff n (g ^ d) =
      ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
  classical
  rw [PowerSeries.coeff_pow]
  let A := (Finset.range d).finsuppAntidiag n
  let B := { l : Fin d → ℕ // ∑ i, l i = n }
  letI : Fintype B := Fintype.ofEquiv A (finsuppAntidiagRangeEquivFin n d)
  let P : B → Prop := fun l => ∀ i, 0 < l.1 i
  let Pos := { l : Fin d → ℕ // (∀ i, 0 < l i) ∧ ∑ i, l i = n }
  letI : Fintype Pos := Fintype.ofEquiv { x : B // P x } (positiveSubtypeEquiv n d)
  have h_antidiag_to_B :
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
        ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
    calc
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
          ∑ a : A, ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g := by
        simpa [A] using (Finset.sum_attach A
          (fun a : ℕ →₀ ℕ => ∏ i ∈ Finset.range d, PowerSeries.coeff (a i) g)).symm
      _ = ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
        exact Fintype.sum_equiv (finsuppAntidiagRangeEquivFin n d)
          (fun a : A => ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g)
          (fun l : B => ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
          (by
            intro a
            calc
              (∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g) =
                  ∏ i : Fin d, PowerSeries.coeff (a.1 i.val) g := by
                exact (Fin.prod_univ_eq_prod_range
                  (fun i => PowerSeries.coeff (a.1 i) g) d).symm
              _ = ∏ i : Fin d,
                    PowerSeries.coeff (((finsuppAntidiagRangeEquivFin n d) a).1 i) g := by
                simp [finsuppAntidiagRangeEquivFin])
  rw [h_antidiag_to_B]
  have h_filter :
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
        ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
    have hsubset : (Finset.univ.filter P) ⊆ (Finset.univ : Finset B) := by
      intro x _hx
      simp
    have hsum_subset :
        ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) =
          ∑ x : B, ∏ i : Fin d, PowerSeries.coeff (x.1 i) g := by
      refine Finset.sum_subset hsubset ?_
      intro x _hx hxnot
      exact prod_coeff_eq_zero_of_not_pos hg x (by simpa [P] using hxnot)
    calc
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
          ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) :=
        hsum_subset.symm
      _ = ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
        refine Finset.sum_subtype (Finset.univ.filter P) ?_
          (fun x : B => ∏ i : Fin d, PowerSeries.coeff (x.1 i) g)
        intro x
        simp [P]
  rw [h_filter]
  calc
    (∑ l : { x : B // P x },
        ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g) =
      ∑ l : Pos,
        ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
      exact Fintype.sum_equiv (positiveSubtypeEquiv n d)
        (fun l : { x : B // P x } =>
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (by intro l; rfl)
    _ = ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      exact Fintype.sum_equiv (positiveFinTupleCompositionEquiv n d)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (fun c : { c : Composition n // c.length = d } =>
          ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g)
        (by
          intro l
          change (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
            ∏ i : Fin (List.ofFn l.1).length,
              PowerSeries.coeff ((List.ofFn l.1).get i) g
          exact Fintype.prod_equiv (finCongr (by simp [List.length_ofFn]))
            (fun i : Fin d => PowerSeries.coeff (l.1 i) g)
            (fun i : Fin (List.ofFn l.1).length =>
              PowerSeries.coeff ((List.ofFn l.1).get i) g)
            (by intro i; simp))

private lemma subst_coeff_eq_sum_composition {f g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst g) =
      ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
  classical
  have hsubst := PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hg) f n
  rw [hsubst]
  simp only [smul_eq_mul]
  let term : ℕ → ℂ := fun d => PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)
  have hsupport : Function.support term ⊆ (Finset.range (n + 1) : Set ℕ) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hmem
    have hnd : n < d := by omega
    have hz : PowerSeries.coeff n (g ^ d) = 0 :=
      coeff_pow_eq_zero_of_constantCoeff_eq_zero hg hnd
    have hdne : term d ≠ 0 := hd
    simp [term, hz] at hdne
  calc
    (∑ᶠ d : ℕ, PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)) =
        ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) := by
      simpa [term] using finsum_eq_sum_of_support_subset term hsupport
    _ = ∑ d ∈ Finset.range (n + 1),
        ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      refine Finset.sum_congr rfl ?_
      intro d _hd
      rw [coeff_pow_eq_sum_composition_length hg d n]
      simp [Finset.mul_sum]
    _ = ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun d => ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g) (n + 1)]
      rw [← Fintype.sum_sigma (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
        PowerSeries.coeff x.1.val f *
          ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)]
      exact Fintype.sum_equiv (sigmaLengthCompositionEquiv n)
        (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
          PowerSeries.coeff x.1.val f *
            ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)
        (fun c : Composition n =>
          PowerSeries.coeff c.length f *
            ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g)
        (by
          intro x
          rcases x with ⟨d, c, hc⟩
          dsimp [sigmaLengthCompositionEquiv]
          apply congrArg₂ HMul.hMul
          · exact congrArg (fun k => PowerSeries.coeff k f) hc.symm
          · rfl)

namespace PowerSeries

theorem toFMLS_subst_eq_comp {f g : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.toFMLS (f.subst g) =
      (PowerSeries.toFMLS f).comp (PowerSeries.toFMLS g) := by
  ext n
  simp [PowerSeries.coeff_toFMLS]
  change PowerSeries.coeff n (f.subst g) =
    ((FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n f)).comp
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n g))).coeff n
  rw [FormalMultilinearSeries.ofScalars_comp_coeff]
  exact subst_coeff_eq_sum_composition hg n

end PowerSeries
end
end

section
/-!
# Saddle-point assembly bricks

This file contains the exact Cauchy parameterization on `[-pi, pi]` and the
bounded algebraic assembly theorem for a central/tail saddle decomposition.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal

noncomputable section

private lemma saddlePhase_periodic (n : ℕ) :
    Function.Periodic (fun θ : ℝ => Complex.exp (-(↑↑n * ↑θ) * Complex.I))
      (2 * Real.pi) := by
  intro θ
  change Complex.exp (-(↑↑n * ↑(θ + 2 * Real.pi)) * Complex.I) =
    Complex.exp (-(↑↑n * ↑θ) * Complex.I)
  rw [show -(↑↑n * ↑(θ + 2 * Real.pi)) * I =
      -(↑↑n * ↑θ) * I - ↑n * (2 * ↑Real.pi * I) by
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    norm_num
    ring_nf]
  exact Complex.exp_periodic.sub_nat_mul_eq n

private lemma saddleRawIntegrand_periodic (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    Function.Periodic (saddleRawIntegrand f r n) (2 * Real.pi) := by
  have hcircle0 :
      Function.Periodic (fun θ : ℝ => f (circleMap (0 : ℂ) r θ)) (2 * Real.pi) :=
    (periodic_circleMap (0 : ℂ) r).comp f
  have hcircle :
      Function.Periodic
        (fun θ : ℝ => f ((r : ℂ) * Complex.exp (θ * Complex.I))) (2 * Real.pi) := by
    simpa [circleMap_zero] using hcircle0
  exact hcircle.mul (saddlePhase_periodic n)

private lemma saddleRawIntegral_zero_to_neg_pi (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ) =
      ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
  have h := (saddleRawIntegrand_periodic f r n).intervalIntegral_add_eq (-Real.pi) 0
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using h.symm

private lemma cauchyCircleIntegrand_param_eq
    (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (n : ℕ) (θ : ℝ) :
    deriv (circleMap (0 : ℂ) r) θ •
      (((1 : ℂ) / (circleMap (0 : ℂ) r θ - 0)) ^ n •
        (circleMap (0 : ℂ) r θ - 0)⁻¹ • f (circleMap (0 : ℂ) r θ)) =
    Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcircle : deriv (circleMap (0 : ℂ) r) θ =
      circleMap (0 : ℂ) r θ * Complex.I :=
    _root_.deriv_circleMap (0 : ℂ) r θ
  rw [hcircle]
  simp [saddleRawIntegrand, circleMap_zero, smul_eq_mul, div_eq_mul_inv,
    mul_pow, Complex.exp_neg, mul_comm, mul_left_comm, mul_assoc]
  field_simp [hrC, Complex.exp_ne_zero]
  rw [← Complex.exp_nat_mul]
  ring_nf

private lemma two_pi_I_inv_mul_I :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) = (2 * Real.pi : ℂ)⁻¹ := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have htwo : (2 * Real.pi : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  field_simp [hI, htwo]

/-- Cauchy's coefficient formula parameterized on the interval `[-pi, pi]`. -/
theorem coeff_eq_saddle_param
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r)) (n : ℕ) :
    p.coeff n =
      (2 * Real.pi : ℂ)⁻¹ * (r : ℂ)⁻¹ ^ n *
        ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
  set_option backward.isDefEq.respectTransparency false in
    have hc := coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt hr hp hd n
    rw [hc]
    rw [circleIntegral]
    have hcongr :
        (∫ θ in (0 : ℝ)..2 * Real.pi,
            deriv (circleMap (0 : ℂ) r) θ •
              (((1 : ℂ) / (circleMap (0 : ℂ) r θ - 0)) ^ n •
                (circleMap (0 : ℂ) r θ - 0)⁻¹ • f (circleMap (0 : ℂ) r θ))) =
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact cauchyCircleIntegrand_param_eq f hr n θ
    rw [hcongr]
    rw [show (∫ θ in (0 : ℝ)..2 * Real.pi,
            Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) =
          Complex.I * ((r : ℂ)⁻¹ ^ n) *
            ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ by
      calc
        (∫ θ in (0 : ℝ)..2 * Real.pi,
            Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ)
            = ∫ θ in (0 : ℝ)..2 * Real.pi,
                Complex.I * (((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) := by
              apply intervalIntegral.integral_congr
              intro θ _
              ring
        _ = Complex.I *
              (∫ θ in (0 : ℝ)..2 * Real.pi,
                ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) := by
              exact intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 2 * Real.pi)
                (μ := MeasureTheory.volume) (r := Complex.I)
                (f := fun θ => ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ)
        _ = Complex.I * (((r : ℂ)⁻¹ ^ n) *
              ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ) := by
              exact congrArg (fun z : ℂ => Complex.I * z)
                (intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 2 * Real.pi)
                  (μ := MeasureTheory.volume) (r := ((r : ℂ)⁻¹ ^ n))
                  (f := fun θ => saddleRawIntegrand f r n θ))
        _ = Complex.I * ((r : ℂ)⁻¹ ^ n) *
              ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ := by
              ring]
    rw [saddleRawIntegral_zero_to_neg_pi]
    calc
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (Complex.I * ((r : ℂ)⁻¹ ^ n) *
            ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ)
          =
            ((((2 * Real.pi : ℂ) * Complex.I)⁻¹) * Complex.I) *
              ((r : ℂ)⁻¹ ^ n) *
                ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
              simp [smul_eq_mul]
              ring
      _ = (2 * Real.pi : ℂ)⁻¹ * (r : ℂ)⁻¹ ^ n *
            ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
              rw [two_pi_I_inv_mul_I]

private lemma saddleRawIntegrand_eq_const_mul_saddleGAt
    (f : ℂ → ℂ) {r : ℝ} (hfnz : f (r : ℂ) ≠ 0) (n : ℕ) (θ : ℝ) :
    saddleRawIntegrand f r n θ = f (r : ℂ) * saddleGAt f r n θ := by
  simp [saddleRawIntegrand, saddleGAt, div_eq_mul_inv, mul_comm, mul_assoc]
  field_simp [hfnz]

/-- Cauchy's parameterization in normalized saddle-integral form. -/
theorem coeff_eq_saddle_param_normalized
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r))
    (hfnz : f (r : ℂ) ≠ 0) (n : ℕ) :
    p.coeff n = saddlePrefAt f r n * saddleJfullAt f r n := by
  rw [coeff_eq_saddle_param hr hp hd n]
  have hraw :
      (∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ) =
        f (r : ℂ) * ∫ θ in (-Real.pi)..Real.pi, saddleGAt f r n θ := by
    calc
      (∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ)
          = ∫ θ in (-Real.pi)..Real.pi, f (r : ℂ) * saddleGAt f r n θ := by
            apply intervalIntegral.integral_congr
            intro θ _
            exact saddleRawIntegrand_eq_const_mul_saddleGAt f hfnz n θ
      _ = f (r : ℂ) * ∫ θ in (-Real.pi)..Real.pi, saddleGAt f r n θ := by
            exact intervalIntegral.integral_const_mul (a := -Real.pi) (b := Real.pi)
              (μ := MeasureTheory.volume) (r := f (r : ℂ)) (f := fun θ => saddleGAt f r n θ)
  rw [hraw]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [saddlePrefAt, saddleJfullAt]
  field_simp [hrC]

/-- Split the full normalized integral into central and tail pieces. -/
theorem saddleJfullAt_eq_saddleJcAt_add_saddleJtAt
    (f : ℂ → ℂ) (r δ : ℝ) (n : ℕ)
    (hleft : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-Real.pi) (-δ))
    (hcenter : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-δ) δ)
    (hright : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume δ Real.pi) :
    saddleJfullAt f r n = saddleJcAt f r δ n + saddleJtAt f r δ n := by
  have h12 := intervalIntegral.integral_add_adjacent_intervals hleft hcenter
  have hfull := intervalIntegral.integral_add_adjacent_intervals (hleft.trans hcenter) hright
  unfold saddleJfullAt saddleJcAt saddleJtAt
  rw [← hfull, ← h12]
  ring

/-- Exact coefficient split into the central window and the two tails. -/
theorem coeff_eq_saddle_split
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r δ : ℝ} {n : ℕ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r))
    (hfnz : f (r : ℂ) ≠ 0)
    (hleft : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-Real.pi) (-δ))
    (hcenter : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-δ) δ)
    (hright : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume δ Real.pi) :
    p.coeff n = saddlePrefAt f r n * (saddleJcAt f r δ n + saddleJtAt f r δ n) := by
  rw [coeff_eq_saddle_param_normalized hr hp hd hfnz n]
  rw [saddleJfullAt_eq_saddleJcAt_add_saddleJtAt f r δ n hleft hcenter hright]

/-- Eventual sequence version of the exact central/tail split. -/
theorem eventually_coeff_eq_saddle_split
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (r δ : ℕ → ℝ)
    (hp : HasFPowerSeriesAt f p 0)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ f (Metric.closedBall 0 (r n)))
    (hfnz : ∀ᶠ n in atTop, f (r n : ℂ) ≠ 0)
    (hleft : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-Real.pi) (-(δ n)))
    (hcenter : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-(δ n)) (δ n))
    (hright : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (δ n) Real.pi) :
    ∀ᶠ n in atTop,
      p.coeff n = saddlePref f r n * (saddleJc f r δ n + saddleJt f r δ n) := by
  filter_upwards [hr, hd, hfnz, hleft, hcenter, hright] with
    n hrn hdn hfnzn hleftn hcentern hrightn
  simpa [saddlePref, saddleJc, saddleJt, saddleG] using
    coeff_eq_saddle_split (f := f) (p := p) (r := r n) (δ := δ n) (n := n)
      hrn hp hdn hfnzn hleftn hcentern hrightn

/-- Assembly theorem from an exact central/tail split and normalized limits. -/
theorem coeff_isEquivalent_saddle_assembly
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (r B δ : ℕ → ℝ)
    (Hsplit : ∀ᶠ n in atTop,
      p.coeff n = saddlePref f r n * (saddleJc f r δ n + saddleJt f r δ n))
    (Hcentral : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
      atTop (𝓝 1))
    (Htail : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f r δ n)
      atTop (𝓝 0))
    (Hnz : ∀ᶠ n in atTop, saddleScale f r B n ≠ 0) :
    (fun n : ℕ => p.coeff n) ~[atTop] (fun n : ℕ => saddleScale f r B n) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  let S : ℕ → ℂ := fun n => (Real.sqrt (2 * Real.pi * B n) : ℂ)
  have hratio :
      (fun n : ℕ => p.coeff n / saddleScale f r B n) =ᶠ[atTop]
        (fun n : ℕ => S n * (saddleJc f r δ n + saddleJt f r δ n)) := by
    filter_upwards [Hsplit, Hnz] with n hsplit hnz
    rw [hsplit]
    dsimp [S, saddleScale]
    have hS : (Real.sqrt (2 * Real.pi * B n) : ℂ) ≠ 0 := by
      intro hzero
      apply hnz
      simp [hzero, saddleScale]
    have hpref : saddlePref f r n ≠ 0 := by
      intro hpref_zero
      apply hnz
      simp [hpref_zero, saddleScale]
    field_simp [hpref, hS]
  have hsum :
      Tendsto (fun n : ℕ => S n * (saddleJc f r δ n + saddleJt f r δ n))
        atTop (𝓝 1) := by
    have hadd :
        Tendsto
          (fun n : ℕ =>
            S n * saddleJc f r δ n + S n * saddleJt f r δ n) atTop (𝓝 1) := by
      simpa [S] using Hcentral.add Htail
    refine Tendsto.congr' ?_ hadd
    exact Eventually.of_forall fun n => by
      dsimp [S]
      ring
  exact Tendsto.congr' hratio.symm hsum

/--
Assembly theorem with the exact split discharged from the Cauchy parameterization
and interval additivity.
-/
theorem coeff_isEquivalent_saddle_assembly_of_cauchy
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (r B δ : ℕ → ℝ)
    (hp : HasFPowerSeriesAt f p 0)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ f (Metric.closedBall 0 (r n)))
    (hfnz : ∀ᶠ n in atTop, f (r n : ℂ) ≠ 0)
    (hleft : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-Real.pi) (-(δ n)))
    (hcenterInt : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-(δ n)) (δ n))
    (hright : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (δ n) Real.pi)
    (Hcentral : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
      atTop (𝓝 1))
    (Htail : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f r δ n)
      atTop (𝓝 0))
    (Hnz : ∀ᶠ n in atTop, saddleScale f r B n ≠ 0) :
    (fun n : ℕ => p.coeff n) ~[atTop] (fun n : ℕ => saddleScale f r B n) :=
  coeff_isEquivalent_saddle_assembly r B δ
    (eventually_coeff_eq_saddle_split r δ hp hr hd hfnz hleft hcenterInt hright)
    Hcentral Htail Hnz

end
end

section
open Complex
open scoped NNReal ENNReal

noncomputable section

theorem expCarrier_toFMLS_eq_expSeries :
    PowerSeries.toFMLS expCarrier = NormedSpace.expSeries ℂ ℂ := by
  rw [NormedSpace.expSeries_eq_ofScalars]
  ext n
  simp [PowerSeries.toFMLS, expCarrier]

@[simp] theorem expCarrier_radius :
    (PowerSeries.toFMLS expCarrier).radius = ⊤ := by
  rw [expCarrier_toFMLS_eq_expSeries]
  exact NormedSpace.expSeries_radius_eq_top ℂ ℂ

end
end

section
/-!
# Gaussian central saddle core

This file packages the reusable dominated-convergence core for the central
Gaussian window after the saddle scaling `theta = x / sqrt (B n)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- The normalized Gaussian integral used by the saddle central window. -/
theorem gaussian_integral_half :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2)) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    have hgauss :=
      integral_gaussian_complex (b := (1 / 2 : ℂ))
        (by norm_num : 0 < (Complex.re (1 / 2 : ℂ)))
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2)) =
        (fun x : ℝ => Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ 2)) by
          funext x
          norm_num
          ring_nf]
    rw [hgauss]
    have hbase : (↑Real.pi / (1 / 2 : ℂ)) = (↑(2 * Real.pi) : ℂ) := by
      norm_num [div_eq_mul_inv]
      ring
    rw [hbase]
    have hexp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hexp]
    rw [← Complex.ofReal_cpow]
    · rw [Complex.ofReal_inj]
      rw [Real.sqrt_eq_rpow]
    · positivity

private lemma saddle_scaled_constant (B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) :
    (Real.sqrt (2 * Real.pi * B n) : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
      ((Real.sqrt (B n))⁻¹ : ℂ) =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) := by
  let c : ℝ := Real.sqrt (B n)
  have hc_pos : 0 < c := by simpa [c] using Real.sqrt_pos.mpr hB
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hsqrt2_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt2_ne : Real.sqrt (2 * Real.pi) ≠ 0 := hsqrt2_pos.ne'
  have hsqrt_prod :
      Real.sqrt (2 * Real.pi * B n) = Real.sqrt (2 * Real.pi) * c := by
    rw [show 2 * Real.pi * B n = (2 * Real.pi) * B n by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  have hconstR :
      Real.sqrt (2 * Real.pi * B n) * (2 * Real.pi)⁻¹ * c⁻¹ =
        1 / Real.sqrt (2 * Real.pi) := by
    rw [hsqrt_prod]
    calc
      (Real.sqrt (2 * Real.pi) * c) * (2 * Real.pi)⁻¹ * c⁻¹
          = Real.sqrt (2 * Real.pi) * (2 * Real.pi)⁻¹ := by
            field_simp [hc_ne]
      _ = Real.sqrt (2 * Real.pi) / (2 * Real.pi) := by
            rw [div_eq_mul_inv]
      _ = Real.sqrt (2 * Real.pi) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)) := by
            congr 1
            rw [← sq]
            rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
      _ = 1 / Real.sqrt (2 * Real.pi) := by
            field_simp [hsqrt2_ne]
  norm_cast

/--
After the scaling `theta = x / sqrt (B n)`, the central saddle integral has
the normalized full Gaussian prefactor.
-/
theorem saddleJc_eq_integral_scaled
    (f : ℂ → ℂ) (r δ B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) :
    (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        ∫ x in -(δ n * Real.sqrt (B n))..(δ n * Real.sqrt (B n)),
          saddleG f r n (x / Real.sqrt (B n)) := by
  let c : ℝ := Real.sqrt (B n)
  have hc_pos : 0 < c := by simpa [c] using Real.sqrt_pos.mpr hB
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hsubst :
      (∫ θ in (-(δ n))..(δ n), saddleG f r n θ) =
        c⁻¹ • ∫ x in -(δ n * c)..(δ n * c), saddleG f r n (x / c) := by
    have h := intervalIntegral.inv_smul_integral_comp_div
      (f := fun θ : ℝ => saddleG f r n θ)
      (a := -(δ n * c)) (b := δ n * c) c
    have hb : δ n * c / c = δ n := by
      exact mul_div_cancel_right₀ (δ n) hc_ne
    have ha : -(δ n * c) / c = -(δ n) := by
      rw [neg_div, hb]
    rw [ha, hb] at h
    exact h.symm
  unfold saddleJc saddleJcAt
  change (Real.sqrt (2 * Real.pi * B n) : ℂ) *
      ((2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-(δ n))..(δ n), saddleG f r n θ) =
    (1 / Real.sqrt (2 * Real.pi) : ℂ) *
      ∫ x in -(δ n * c)..(δ n * c), saddleG f r n (x / c)
  rw [hsubst]
  rw [show ((c⁻¹ : ℝ) •
        ∫ (x : ℝ) in -(δ n * c)..δ n * c, saddleG f r n (x / c)) =
      ((c⁻¹ : ℂ) *
        ∫ (x : ℝ) in -(δ n * c)..δ n * c, saddleG f r n (x / c)) by
        simp]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [show (Real.sqrt (2 * Real.pi * B n) : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
      (c⁻¹ : ℂ) = (1 / Real.sqrt (2 * Real.pi) : ℂ) by
        simpa [c] using saddle_scaled_constant B n hB]

private lemma Hfun_eq_indicator (f : ℂ → ℂ) (r B δ : ℕ → ℝ) (n : ℕ) :
    Hfun f r B δ n =
      Set.indicator (Set.Icc (-(δ n * Real.sqrt (B n))) (δ n * Real.sqrt (B n)))
        (fun x : ℝ => saddleG f r n (x / Real.sqrt (B n))) := by
  funext x
  simp [Hfun, Set.indicator, abs_le]

private lemma integral_Hfun_eq_interval
    (f : ℂ → ℂ) (r B δ : ℕ → ℝ) (n : ℕ)
    (hL : 0 ≤ δ n * Real.sqrt (B n)) :
    (∫ x : ℝ, Hfun f r B δ n x) =
      ∫ x in -(δ n * Real.sqrt (B n))..(δ n * Real.sqrt (B n)),
        saddleG f r n (x / Real.sqrt (B n)) := by
  let L : ℝ := δ n * Real.sqrt (B n)
  let g : ℝ → ℂ := fun x => saddleG f r n (x / Real.sqrt (B n))
  have hle : -L ≤ L := by linarith [hL]
  calc
    (∫ x : ℝ, Hfun f r B δ n x) =
        ∫ x : ℝ, Set.indicator (Set.Icc (-L) L) g x := by
          simp [Hfun_eq_indicator, L, g]
    _ = ∫ x in Set.Icc (-L) L, g x := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ x in Set.Ioc (-L) L, g x := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ x in (-L)..L, g x := by
          rw [intervalIntegral.integral_of_le hle]

/--
Dominated-convergence central Gaussian core, with the measurability hypothesis
required by Mathlib's DCT stated explicitly.
-/
theorem central_tendsto_one_of_dominated_of_aestronglyMeasurable
    (f : ℂ → ℂ) (r B δ : ℕ → ℝ)
    (hBpos : ∀ᶠ n in atTop, 0 < B n)
    (hL : Tendsto (fun n : ℕ => δ n * Real.sqrt (B n)) atTop atTop)
    (Hmeas :
      ∀ᶠ n in atTop,
        AEStronglyMeasurable (Hfun f r B δ n) MeasureTheory.volume)
    (Hpoint :
      ∀ᵐ x : ℝ,
        Tendsto (fun n : ℕ => Hfun f r B δ n x) atTop
          (𝓝 (Complex.exp (-(x ^ 2) / 2))))
    (D : ℝ → ℝ) (hDint : Integrable D)
    (Hdom :
      ∀ᶠ n in atTop, ∀ᵐ x : ℝ, ‖Hfun f r B δ n x‖ ≤ D x) :
    Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
      atTop (𝓝 1) := by
  have hInt_tendsto :
      Tendsto (fun n : ℕ => ∫ x : ℝ, Hfun f r B δ n x) atTop
        (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2))) := by
    exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume) (bound := D) Hmeas Hdom hDint Hpoint
  have hsqrt2_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt2_ne : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt2_pos.ne'
  have hscaled :
      Tendsto
        (fun n : ℕ => (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          ∫ x : ℝ, Hfun f r B δ n x)
        atTop (𝓝 1) := by
    have hmul := hInt_tendsto.const_mul (1 / Real.sqrt (2 * Real.pi) : ℂ)
    have hconst :
        (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2)) = 1 := by
      rw [gaussian_integral_half]
      field_simp [hsqrt2_ne]
    simpa only [hconst] using hmul
  have hLnonneg : ∀ᶠ n in atTop, 0 ≤ δ n * Real.sqrt (B n) :=
    hL.eventually_ge_atTop 0
  have heq :
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
        =ᶠ[atTop]
      (fun n : ℕ => (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        ∫ x : ℝ, Hfun f r B δ n x) := by
    filter_upwards [hBpos, hLnonneg] with n hBn hLn
    rw [saddleJc_eq_integral_scaled f r δ B n hBn]
    rw [← integral_Hfun_eq_interval f r B δ n hLn]
  exact Tendsto.congr' heq.symm hscaled

end
end

section
/-!
# The exponential saddle testbed

This file instantiates the saddle assembly machinery for `f z = exp z`.
The hard local-analysis estimates are isolated as explicitly documented
lemmas: the second-order exponential limit, the central domination estimate,
and the tail estimate.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

namespace ExpStirling

lemma expCarrier_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS expCarrier) (0 : ℂ) := by
  simpa [expSeriesC] using
    (show HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS expCarrier) (0 : ℂ) by
      simpa [_root_.expCarrier_toFMLS_eq_expSeries] using exp_hasFPowerSeriesAt_zero)

end ExpStirling
end
end

section
/-!
# H-admissible saddle-point bridge

This file packages the abstract H-admissible hypotheses needed to feed the
central Gaussian core, the tail estimate, and the Cauchy assembly theorem.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

lemma saddleGAt_eq_gaussian_mul_saddleLocalRatio
    (f : ℂ → ℂ) (a b : ℝ → ℝ) (r x : ℝ) (n : ℕ)
    (hb : 0 < b r) (ha : a r = (n : ℝ)) :
    saddleGAt f r n (x / Real.sqrt (b r)) =
      Complex.exp (-(x ^ 2) / 2) *
        saddleLocalRatio f a b r (x / Real.sqrt (b r)) := by
  let θ : ℝ := x / Real.sqrt (b r)
  have hsqrt_pos : 0 < Real.sqrt (b r) := Real.sqrt_pos.mpr hb
  have hsqrt_ne : Real.sqrt (b r) ≠ 0 := hsqrt_pos.ne'
  have hquad : b r * θ ^ 2 / 2 = x ^ 2 / 2 := by
    dsimp [θ]
    rw [div_pow]
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt hb.le]
    ring
  have hphaseR : (n : ℝ) * θ = a r * θ := by
    rw [ha]
  have hphaseC :
      Complex.exp (-(↑↑n * ↑θ) * I) =
        Complex.exp (-(a r * θ : ℝ) * I) := by
    congr 1
    have hmulC : (n : ℂ) * (θ : ℂ) = ((a r * θ : ℝ) : ℂ) := by
      exact_mod_cast hphaseR
    rw [hmulC]
  have hden :
      Complex.exp (-(b r * θ ^ 2 / 2 : ℝ)) =
        Complex.exp ((-(x ^ 2) / 2 : ℝ) : ℂ) := by
    congr 1
    exact_mod_cast (by linarith [hquad] :
      -(b r * θ ^ 2 / 2) = -(x ^ 2) / 2)
  have hgauss :
      Complex.exp (-(x ^ 2) / 2) =
        Complex.exp ((-(x ^ 2) / 2 : ℝ) : ℂ) := by
    congr 1
    norm_num
  dsimp [θ] at hphaseC hden ⊢
  rw [hgauss]
  unfold saddleGAt saddleLocalRatio
  rw [hphaseC, hden]
  field_simp [Complex.exp_ne_zero ((-(x ^ 2) / 2 : ℝ) : ℂ)]

lemma Hfun_eq_gaussian_mul_saddleLocalRatio
    (f : ℂ → ℂ) (a b : ℝ → ℝ) (R δ : ℕ → ℝ) (n : ℕ) (x : ℝ)
    (hb : 0 < b (R n)) (ha : a (R n) = (n : ℝ))
    (hx : |x| ≤ δ n * Real.sqrt (b (R n))) :
    Hfun f R (fun n => b (R n)) δ n x =
      Complex.exp (-(x ^ 2) / 2) *
        saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))) := by
  simpa [Hfun, saddleG, hx] using
    saddleGAt_eq_gaussian_mul_saddleLocalRatio f a b (R n) x n hb ha

lemma theta_mem_local_window_of_scaled_window
    (x δ B : ℝ) (hB : 0 < B)
    (hx : |x| ≤ δ * Real.sqrt B) :
    |x / Real.sqrt B| ≤ δ := by
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  rw [abs_div, abs_of_pos hsqrt]
  exact (div_le_iff₀ hsqrt).mpr hx

lemma saddleLocalRatio_tendsto_one_of_localUniform
    {F : Filter ℝ} (f : ℂ → ℂ) (a b δr : ℝ → ℝ)
    (R : ℕ → ℝ) (x : ℝ)
    (hR : Tendsto R atTop F)
    (hlocal :
      ∀ ε > 0, ∀ᶠ r in F, ∀ θ : ℝ,
        |θ| ≤ δr r →
          ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε)
    (hBpos : ∀ᶠ n in atTop, 0 < b (R n))
    (hL :
      Tendsto
        (fun n : ℕ => δr (R n) * Real.sqrt (b (R n)))
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))))
      atTop (𝓝 (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hlocR :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        |θ| ≤ δr (R n) →
          ‖saddleLocalRatio f a b (R n) θ - 1‖ ≤ ε / 2 :=
    hR.eventually (hlocal (ε / 2) hε2)
  have hinside :
      ∀ᶠ n in atTop,
        |x| ≤ δr (R n) * Real.sqrt (b (R n)) :=
    hL.eventually_ge_atTop |x|
  filter_upwards [hlocR, hBpos, hinside] with n hloc hBn hxn
  have htheta :
      |x / Real.sqrt (b (R n))| ≤ δr (R n) :=
    theta_mem_local_window_of_scaled_window x (δr (R n)) (b (R n)) hBn hxn
  have hnorm :
      ‖saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))) - 1‖ ≤ ε / 2 :=
    hloc _ htheta
  have hdist :
      dist (saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))) 1 ≤ ε / 2 := by
    simpa [dist_eq_norm] using hnorm
  exact lt_of_le_of_lt hdist (half_lt_self hε)

lemma Hfun_pointwise_of_localUniform
    {F : Filter ℝ} (f : ℂ → ℂ) (a b δr : ℝ → ℝ)
    (R : ℕ → ℝ)
    (hR : Tendsto R atTop F)
    (hlocal :
      ∀ ε > 0, ∀ᶠ r in F, ∀ θ : ℝ,
        |θ| ≤ δr r →
          ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε)
    (hBpos : ∀ᶠ n in atTop, 0 < b (R n))
    (hL :
      Tendsto
        (fun n : ℕ => δr (R n) * Real.sqrt (b (R n)))
        atTop atTop)
    (hsaddle : ∀ᶠ n in atTop, a (R n) = (n : ℝ)) :
    ∀ᵐ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          Hfun f R (fun n => b (R n)) (fun n => δr (R n)) n x)
        atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
  refine ae_of_all _ fun x => ?_
  have hratio :=
    saddleLocalRatio_tendsto_one_of_localUniform
      f a b δr R x hR hlocal hBpos hL
  have hmul :
      Tendsto
        (fun n : ℕ =>
          Complex.exp (-(x ^ 2) / 2) *
            saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))))
        atTop (𝓝 (Complex.exp (-(x ^ 2) / 2) * 1)) :=
    tendsto_const_nhds.mul hratio
  have htarget :
      Tendsto
        (fun n : ℕ =>
          Complex.exp (-(x ^ 2) / 2) *
            saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))))
        atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
    simpa using hmul
  have hinside :
      ∀ᶠ n in atTop,
        |x| ≤ δr (R n) * Real.sqrt (b (R n)) :=
    hL.eventually_ge_atTop |x|
  have heq :
      (fun n : ℕ =>
          Hfun f R (fun n => b (R n)) (fun n => δr (R n)) n x) =ᶠ[atTop]
        (fun n : ℕ =>
          Complex.exp (-(x ^ 2) / 2) *
            saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))) := by
    filter_upwards [hBpos, hsaddle, hinside] with n hBn han hxn
    exact Hfun_eq_gaussian_mul_saddleLocalRatio
      f a b R (fun n => δr (R n)) n x hBn han hxn
  exact Tendsto.congr' heq.symm htarget

lemma saddleGAt_continuous_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    Continuous fun θ : ℝ => saddleGAt f r n θ := by
  have hfcirc0 : Continuous fun θ : ℝ => f (circleMap (0 : ℂ) r θ) :=
    hf.continuousOn.comp_continuous (continuous_circleMap (0 : ℂ) r)
      (fun θ => circleMap_mem_closedBall (0 : ℂ) hr θ)
  have hfcirc :
      Continuous fun θ : ℝ =>
        f ((r : ℂ) * Complex.exp (θ * Complex.I)) := by
    simpa [circleMap_zero] using hfcirc0
  have hphase :
      Continuous fun θ : ℝ => Complex.exp (-(↑↑n * ↑θ) * I) := by
    fun_prop
  simpa [saddleGAt, div_eq_mul_inv] using
    (hfcirc.mul continuous_const).mul hphase

lemma saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (a b : ℝ) (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    IntervalIntegrable (saddleGAt f r n) volume a b :=
  (saddleGAt_continuous_of_differentiableOn_closedBall f r n hr hf).intervalIntegrable a b

lemma Hfun_aestronglyMeasurable_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (R B δ : ℕ → ℝ) (n : ℕ)
    (hr : 0 ≤ R n)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (R n))) :
    AEStronglyMeasurable (Hfun f R B δ n) volume := by
  classical
  let L : ℝ := δ n * Real.sqrt (B n)
  let g : ℝ → ℂ := fun x => saddleG f R n (x / Real.sqrt (B n))
  have hgcont : Continuous g := by
    have h0 := saddleGAt_continuous_of_differentiableOn_closedBall f (R n) n hr hf
    have hdiv : Continuous fun x : ℝ => x / Real.sqrt (B n) := by
      fun_prop
    simpa [g, saddleG] using h0.comp hdiv
  have hsm : StronglyMeasurable (Set.indicator (Set.Icc (-L) L) g) :=
    hgcont.stronglyMeasurable.indicator measurableSet_Icc
  have heq :
      Hfun f R B δ n =
        Set.indicator (Set.Icc (-L) L) g := by
    funext x
    simp [Hfun, Set.indicator, abs_le, L, g]
  rw [heq]
  exact hsm.aestronglyMeasurable

lemma Hfun_aestronglyMeasurable_eventually_of_sequence
    {F : Filter ℝ} (f : ℂ → ℂ) (R B δ : ℕ → ℝ)
    (hR : Tendsto R atTop F)
    (hrpos : ∀ᶠ r in F, 0 < r)
    (hdiff :
      ∀ᶠ r in F,
        DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    ∀ᶠ n in atTop,
      AEStronglyMeasurable (Hfun f R B δ n) volume := by
  filter_upwards [hR.eventually hrpos, hR.eventually hdiff] with n hrn hdiffn
  exact Hfun_aestronglyMeasurable_of_differentiableOn_closedBall
    f R B δ n hrn.le hdiffn

lemma centralD_integrable : Integrable centralD := by
  unfold centralD
  have hbase :
      Integrable
        (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
    integrable_exp_neg_mul_sq
      (by norm_num : 0 < (1 / 2 : ℝ))
  have hconst := hbase.const_mul 2
  convert hconst using 1
  funext x
  congr 1
  ring_nf

lemma saddleLocalRatio_norm_le_two_of_norm_sub_one_le_one
    {z : ℂ} (hz : ‖z - 1‖ ≤ (1 : ℝ)) : ‖z‖ ≤ 2 := by
  have hz_eq : z = (z - 1) + 1 := by ring
  calc
    ‖z‖ = ‖(z - 1) + 1‖ := by
      exact congrArg norm hz_eq
    _ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add hz (by norm_num)
    _ = 2 := by norm_num

lemma Hfun_dominated_of_localUniform
    {F : Filter ℝ} (f : ℂ → ℂ) (a b δr : ℝ → ℝ)
    (R : ℕ → ℝ)
    (hR : Tendsto R atTop F)
    (hlocal :
      ∀ ε > 0, ∀ᶠ r in F, ∀ θ : ℝ,
        |θ| ≤ δr r →
          ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε)
    (hBpos : ∀ᶠ n in atTop, 0 < b (R n))
    (hsaddle : ∀ᶠ n in atTop, a (R n) = (n : ℝ)) :
    ∀ᶠ n in atTop, ∀ᵐ x : ℝ,
      ‖Hfun f R (fun n => b (R n)) (fun n => δr (R n)) n x‖
        ≤ centralD x := by
  have hlocR :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        |θ| ≤ δr (R n) →
          ‖saddleLocalRatio f a b (R n) θ - 1‖ ≤ (1 : ℝ) :=
    hR.eventually (hlocal 1 (by norm_num))
  filter_upwards [hlocR, hBpos, hsaddle] with n hloc hBn han
  refine ae_of_all _ fun x => ?_
  by_cases hx : |x| ≤ δr (R n) * Real.sqrt (b (R n))
  · rw [Hfun_eq_gaussian_mul_saddleLocalRatio
      f a b R (fun n => δr (R n)) n x hBn han hx]
    rw [norm_mul]
    have htheta :
        |x / Real.sqrt (b (R n))| ≤ δr (R n) :=
      theta_mem_local_window_of_scaled_window x (δr (R n)) (b (R n)) hBn hx
    have hratio :
        ‖saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))‖ ≤ 2 :=
      saddleLocalRatio_norm_le_two_of_norm_sub_one_le_one (hloc _ htheta)
    have hnormexp :
        ‖Complex.exp (-(x ^ 2) / 2)‖ =
          Real.exp (-(x ^ 2) / 2) := by
      simp [Complex.norm_exp, sq]
    rw [hnormexp]
    calc
      Real.exp (-(x ^ 2) / 2) *
          ‖saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))‖
          ≤ Real.exp (-(x ^ 2) / 2) * 2 :=
            mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
      _ = centralD x := by
            simp [centralD, mul_comm]
  · simp [Hfun, hx, centralD]
    positivity

theorem central_tendsto_one_of_hadmissible
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJc f hr.r (HAdmissible.Δ hf hr) n)
      atTop (𝓝 1) := by
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hL :
      Tendsto
        (fun n : ℕ =>
          HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))
        atTop atTop := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have Hmeas :
      ∀ᶠ n in atTop,
        AEStronglyMeasurable
          (Hfun f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) n) volume :=
    Hfun_aestronglyMeasurable_eventually_of_sequence
      f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr)
      hr.tendsTo hf.r_pos hf.differentiableOn
  have Hpoint :
      ∀ᵐ x : ℝ,
        Tendsto
          (fun n : ℕ =>
            Hfun f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) n x)
          atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      Hfun_pointwise_of_localUniform
        f hf.a hf.b hf.δ hr.r hr.tendsTo hf.local_uniform
        (by simpa [HAdmissible.B] using hBpos)
        (by simpa [HAdmissible.B, HAdmissible.Δ] using hL)
        hr.saddle_eq
  have Hdom :
      ∀ᶠ n in atTop, ∀ᵐ x : ℝ,
        ‖Hfun f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) n x‖
          ≤ centralD x := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      Hfun_dominated_of_localUniform
        f hf.a hf.b hf.δ hr.r hr.tendsTo hf.local_uniform
        (by simpa [HAdmissible.B] using hBpos)
        hr.saddle_eq
  exact central_tendsto_one_of_dominated_of_aestronglyMeasurable
    f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr)
    hBpos hL Hmeas Hpoint centralD centralD_integrable Hdom

lemma saddleJtAt_norm_le_of_tail_bound
    (f : ℂ → ℂ) (r δ E : ℝ) (n : ℕ)
    (hδ_nonneg : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (hE_nonneg : 0 ≤ E)
    (htail : ∀ θ : ℝ, δ ≤ |θ| → |θ| ≤ Real.pi →
      ‖saddleGAt f r n θ‖ ≤ E) :
    ‖saddleJtAt f r δ n‖ ≤
      (‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)) * E := by
  have hleft :
      ‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ ≤
        E * |(-δ) - (-Real.pi)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro θ hθ
    have hθI : -Real.pi < θ ∧ θ ≤ -δ := by
      simpa [Set.uIoc_of_le (by linarith : -Real.pi ≤ -δ)] using hθ
    have hθ_nonpos : θ ≤ 0 := by linarith
    have hδθ : δ ≤ |θ| := by
      rw [abs_of_nonpos hθ_nonpos]
      linarith
    have hθπ : |θ| ≤ Real.pi := by
      rw [abs_of_nonpos hθ_nonpos]
      linarith
    exact htail θ hδθ hθπ
  have hright :
      ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖ ≤
        E * |Real.pi - δ| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro θ hθ
    have hθI : δ < θ ∧ θ ≤ Real.pi := by
      simpa [Set.uIoc_of_le hδπ] using hθ
    have hθ_nonneg : 0 ≤ θ := by linarith
    have hδθ : δ ≤ |θ| := by
      rw [abs_of_nonneg hθ_nonneg]
      linarith
    have hθπ : |θ| ≤ Real.pi := by
      rw [abs_of_nonneg hθ_nonneg]
      exact hθI.2
    exact htail θ hδθ hθπ
  have hlen_right : |Real.pi - δ| ≤ Real.pi := by
    rw [abs_of_nonneg (sub_nonneg.mpr hδπ)]
    linarith [Real.pi_pos]
  have hlen_left : |(-δ) - (-Real.pi)| ≤ Real.pi := by
    rw [show (-δ) - (-Real.pi) = Real.pi - δ by ring]
    exact hlen_right
  have hleft_pi :
      ‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ ≤
        E * Real.pi :=
    hleft.trans (mul_le_mul_of_nonneg_left hlen_left hE_nonneg)
  have hright_pi :
      ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖ ≤
        E * Real.pi :=
    hright.trans (mul_le_mul_of_nonneg_left hlen_right hE_nonneg)
  unfold saddleJtAt
  calc
    ‖(2 * Real.pi : ℂ)⁻¹ *
        ((∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ) +
          ∫ θ in δ..Real.pi, saddleGAt f r n θ)‖
        ≤ ‖((2 * Real.pi : ℂ)⁻¹)‖ *
          (‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ +
            ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖((2 * Real.pi : ℂ)⁻¹)‖ * (E * Real.pi + E * Real.pi) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hleft_pi hright_pi) (norm_nonneg _)
    _ = (‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)) * E := by
          ring

lemma tail_tendsto_zero_of_tailUniform
    (f : ℂ → ℂ) (R B Δ E : ℕ → ℝ)
    (hBpos : ∀ᶠ n in atTop, 0 < B n)
    (hδ_nonneg : ∀ᶠ n in atTop, 0 ≤ Δ n)
    (hδπ : ∀ᶠ n in atTop, Δ n ≤ Real.pi)
    (hE_nonneg : ∀ᶠ n in atTop, 0 ≤ E n)
    (htail : ∀ᶠ n in atTop, ∀ θ : ℝ,
      Δ n ≤ |θ| → |θ| ≤ Real.pi → ‖saddleG f R n θ‖ ≤ E n)
    (hdecay : Tendsto
      (fun n : ℕ => Real.sqrt (2 * Real.pi * B n) * E n) atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n)
      atTop (𝓝 0) := by
  let K : ℝ := ‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)
  have hdecayK :
      Tendsto (fun n : ℕ => K * (Real.sqrt (2 * Real.pi * B n) * E n))
        atTop (𝓝 0) := by
    simpa using hdecay.const_mul K
  have hbound :
      ∀ᶠ n in atTop,
        ‖(Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n‖ ≤
          K * (Real.sqrt (2 * Real.pi * B n) * E n) := by
    filter_upwards [hBpos, hδ_nonneg, hδπ, hE_nonneg, htail] with
      n hBn hδn hδπn hEn htailn
    have hJ : ‖saddleJt f R Δ n‖ ≤ K * E n := by
      simpa [saddleJt, saddleG, K] using
        saddleJtAt_norm_le_of_tail_bound f (R n) (Δ n) (E n) n
          hδn hδπn hEn (fun θ hδθ hθπ => htailn θ hδθ hθπ)
    calc
      ‖(Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n‖
          = Real.sqrt (2 * Real.pi * B n) * ‖saddleJt f R Δ n‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (2 * Real.pi * B n) * (K * E n) :=
            mul_le_mul_of_nonneg_left hJ (Real.sqrt_nonneg _)
      _ = K * (Real.sqrt (2 * Real.pi * B n) * E n) := by
            ring
  have hnorm :
      Tendsto
        (fun n : ℕ =>
          ‖(Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n‖)
        atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hdecayK
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact hnorm

theorem tail_tendsto_zero_of_hadmissible
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJt f hr.r (HAdmissible.Δ hf hr) n)
      atTop (𝓝 0) := by
  rcases hf.tail_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hδ_nonneg : ∀ᶠ n in atTop, 0 ≤ HAdmissible.Δ hf hr n := by
    filter_upwards [hr.tendsTo.eventually hf.δ_pos] with n hδn
    exact hδn.le
  have hδπ : ∀ᶠ n in atTop, HAdmissible.Δ hf hr n ≤ Real.pi := by
    simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_le_pi
  have hE_nonneg_seq : ∀ᶠ n in atTop, 0 ≤ E (hr.r n) := by
    simpa using hr.tendsTo.eventually hE_nonneg
  have htailSeq :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        HAdmissible.Δ hf hr n ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleG f hr.r n θ‖ ≤ E (hr.r n) := by
    filter_upwards [hr.tendsTo.eventually htail] with n htailn θ hδθ hθπ
    simpa [HAdmissible.Δ, saddleG] using htailn n θ hδθ hθπ
  have hdecaySeq :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n))
        atTop (𝓝 0) := by
    simpa [HAdmissible.B] using hdecay.comp hr.tendsTo
  exact tail_tendsto_zero_of_tailUniform
    f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) (fun n => E (hr.r n))
    hBpos hδ_nonneg hδπ hE_nonneg_seq htailSeq hdecaySeq

lemma f_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro hzero
  simp [hzero] at hz

lemma saddleScale_nonzero_of_pos
    (f : ℂ → ℂ) (r B : ℕ → ℝ) (n : ℕ)
    (hr : 0 < r n) (hf : 0 < (f (r n : ℂ)).re) (hB : 0 < B n) :
    saddleScale f r B n ≠ 0 := by
  have hfnz : f (r n : ℂ) ≠ 0 := f_ne_zero_of_re_pos hf
  have hrC : (r n : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hpow : (r n : ℂ) ^ n ≠ 0 := pow_ne_zero n hrC
  have hpref : saddlePref f r n ≠ 0 := by
    unfold saddlePref saddlePrefAt
    exact div_ne_zero hfnz hpow
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * B n) := by
    exact Real.sqrt_pos.mpr (by positivity)
  have hsqrtC : (Real.sqrt (2 * Real.pi * B n) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_pos.ne'
  unfold saddleScale
  exact div_ne_zero hpref hsqrtC

theorem coeff_isEquivalent_saddle_of_hadmissible_limits
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf)
    (Hcentral : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        saddleJc f hr.r (HAdmissible.Δ hf hr) n) atTop (𝓝 1))
    (Htail : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        saddleJt f hr.r (HAdmissible.Δ hf hr) n) atTop (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale f hr.r (HAdmissible.B hf hr) n) := by
  have hrpos : ∀ᶠ n in atTop, 0 < hr.r n := by
    simpa using hr.tendsTo.eventually hf.r_pos
  have hdiff :
      ∀ᶠ n in atTop,
        DifferentiableOn ℂ f (Metric.closedBall 0 (hr.r n)) := by
    simpa using hr.tendsTo.eventually hf.differentiableOn
  have hfnz : ∀ᶠ n in atTop, f (hr.r n : ℂ) ≠ 0 := by
    filter_upwards [hr.tendsTo.eventually hf.f_pos] with n hpos
    exact f_ne_zero_of_re_pos hpos
  have hleft :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (-Real.pi) (-(HAdmissible.Δ hf hr n)) := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (-Real.pi) (-(HAdmissible.Δ hf hr n)) hrn.le hdn
  have hcenter :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (-(HAdmissible.Δ hf hr n)) (HAdmissible.Δ hf hr n) := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (-(HAdmissible.Δ hf hr n)) (HAdmissible.Δ hf hr n) hrn.le hdn
  have hright :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (HAdmissible.Δ hf hr n) Real.pi := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (HAdmissible.Δ hf hr n) Real.pi hrn.le hdn
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have Hnz : ∀ᶠ n in atTop, saddleScale f hr.r (HAdmissible.B hf hr) n ≠ 0 := by
    filter_upwards [hrpos, hr.tendsTo.eventually hf.f_pos, hBpos] with n hrn hfn hBn
    exact saddleScale_nonzero_of_pos f hr.r (HAdmissible.B hf hr) n hrn hfn hBn
  exact coeff_isEquivalent_saddle_assembly_of_cauchy
    hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr)
    hf.hp hrpos hdiff hfnz hleft hcenter hright Hcentral Htail Hnz

theorem coeff_isEquivalent_saddle
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale f hr.r (HAdmissible.B hf hr) n) :=
  coeff_isEquivalent_saddle_of_hadmissible_limits hf hr
    (central_tendsto_one_of_hadmissible hf hr)
    (tail_tendsto_zero_of_hadmissible hf hr)

end
end

section
/-!
# Involution H-admissible saddle data

This file records the Hayman data for the involution EGF
`exp (z + z^2 / 2)`.  The saddle data are
`a(r)=r+r^2`, `b(r)=r+2r^2`, and `δ(r)=r^(-3/4)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace InvolutionHAdmissible

/-- The genuine complex EGF carrier coming from the Ch2 involution class. -/
def involCarrier : PowerSeries ℂ :=
  PowerSeries.mapℂ AnalyticCombinatorics.Ch1.CombClass.parts12.set.egf

@[simp] theorem involCarrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n involCarrier = (involCoeffR n : ℂ) := by
  simp [involCarrier, involCoeffR, AnalyticCombinatorics.Ch1.CombClass.coeff_egf]

lemma hasFPowerSeriesAt_id_toFMLS_X :
    HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n • (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)).coeff n
  have hsingle : HasSum term (term 1) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

lemma hasFPowerSeriesAt_mul_toFMLS {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : HasFPowerSeriesAt f (PowerSeries.toFMLS F) (0 : ℂ))
    (hg : HasFPowerSeriesAt g (PowerSeries.toFMLS G) (0 : ℂ)) :
    HasFPowerSeriesAt (fun z : ℂ => f z * g z)
      (PowerSeries.toFMLS (F * G)) (0 : ℂ) := by
  rcases hf with ⟨rf, hrf⟩
  rcases hg with ⟨rg, hrg⟩
  rw [hasFPowerSeriesAt_iff]
  refine eventually_of_mem
    (Metric.eball_mem_nhds (0 : ℂ) (lt_min hrf.r_pos hrg.r_pos)) ?_
  intro z hz
  have hzf : z ∈ Metric.eball (0 : ℂ) rf := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_left _ _))
  have hzg : z ∈ Metric.eball (0 : ℂ) rg := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_right _ _))
  let a : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n F
  let b : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n G
  have hsumf : HasSum a (f z) := by
    have h := hrf.hasSum hzf
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hsumg : HasSum b (g z) := by
    have h := hrg.hasSum hzg
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hzfrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS F).radius :=
    Metric.eball_subset_eball hrf.r_le hzf
  have hzgrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS G).radius :=
    Metric.eball_subset_eball hrg.r_le hzg
  have hnormf : Summable fun n : ℕ => ‖a n‖ := by
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS F).summable_norm_apply hzfrad
  have hnormg : Summable fun n : ℕ => ‖b n‖ := by
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS G).summable_norm_apply hzgrad
  let cseq : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n (F * G)
  let d : ℕ → ℂ := fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
  have hcd : ∀ n, cseq n = d n := by
    intro n
    change z ^ n * PowerSeries.coeff (R := ℂ) n (F * G) =
      ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro kl hkl
    have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    simp [a, b]
    rw [← hsum, pow_add]
    ring
  have hnormd : Summable fun n : ℕ => ‖d n‖ := by
    simpa [d] using summable_norm_sum_mul_antidiagonal_of_summable_norm hnormf hnormg
  have hnormc : Summable fun n : ℕ => ‖cseq n‖ := by
    exact hnormd.congr (fun n => by rw [hcd n])
  have hsumc : Summable cseq := hnormc.of_norm
  have htsum : (∑' n : ℕ, cseq n) = f z * g z := by
    have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnormf hnormg
    rw [hsumf.tsum_eq, hsumg.tsum_eq] at hprod
    rw [tsum_congr hcd, ← hprod]
  have hmain : HasSum cseq (f z * g z) := hsumc.hasSum_iff.mpr htsum
  simpa [cseq, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hmain

/-- Continuous involution saddle mean, `a(r)=r+r^2`. -/
def involSaddleAReal (r : ℝ) : ℝ :=
  r + r ^ 2

/-- Hayman window for the involution saddle. -/
def involSaddleDeltaReal (r : ℝ) : ℝ :=
  r ^ (-(3 / 4 : ℝ))

@[simp] lemma involSaddleAReal_apply (r : ℝ) :
    involSaddleAReal r = r + r ^ 2 := rfl

@[simp] lemma involSaddleBReal_apply (r : ℝ) :
    involSaddleBReal r = r + 2 * r ^ 2 := rfl

@[simp] lemma involSaddleDeltaReal_apply (r : ℝ) :
    involSaddleDeltaReal r = r ^ (-(3 / 4 : ℝ)) := rfl

end InvolutionHAdmissible
end
end

section
/-!
# Blocks of size at most three: H-admissible saddle data

This file records the Hayman data for the EGF
`exp (z + z^2/2 + z^3/6)`, the labelled SET class whose components have
sizes `1`, `2`, or `3`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma CombClass.counts_parts123 (n : ℕ) :
    CombClass.parts123.counts n =
      if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 1 else 0 :=
  Fintype.card_fin _

/-- The EGF of the size-`1`, `2`, `3` component class is `z + z^2/2 + z^3/6`. -/
theorem CombClass.egf_parts123_egf :
    CombClass.parts123.egf =
      X + (2⁻¹ : ℚ) • X ^ 2 + (6⁻¹ : ℚ) • X ^ 3 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_parts123, map_add, map_add, coeff_X,
    map_smul, map_smul, coeff_X_pow, coeff_X_pow, smul_eq_mul, smul_eq_mul]
  by_cases h1 : n = 1
  · subst n
    norm_num [Nat.factorial]
  by_cases h2 : n = 2
  · subst n
    norm_num [Nat.factorial]
  by_cases h3 : n = 3
  · subst n
    norm_num [Nat.factorial]
  simp [h1, h2, h3]

/-- The EGF of set partitions into blocks of size at most `3`. -/
theorem CombClass.egf_blocks3 :
    CombClass.blocks3.egf =
      (PowerSeries.exp ℚ).subst
        (X + (2⁻¹ : ℚ) • X ^ 2 + (6⁻¹ : ℚ) • X ^ 3) := by
  rw [CombClass.egf_set _ (by simp [CombClass.counts_parts123]),
    CombClass.egf_parts123_egf]

end AnalyticCombinatorics.Ch1

namespace Blocks3HAdmissible

/-- The genuine complex EGF carrier from the Ch2 labelled SET construction. -/
def blocks3Carrier : PowerSeries ℂ :=
  PowerSeries.mapℂ AnalyticCombinatorics.Ch1.CombClass.blocks3.egf

@[simp] theorem blocks3Carrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n blocks3Carrier = (blocks3CoeffR n : ℂ) := by
  simp [blocks3Carrier, blocks3CoeffR, AnalyticCombinatorics.Ch1.CombClass.coeff_egf]

/-- The formal series used by the H-admissible interface. -/
noncomputable abbrev blocks3Series : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS blocks3Carrier

/-- The cubic inner PowerSeries `z + z^2/2 + z^3/6`. -/
def blocks3InnerPS : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) +
    (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2 +
      (6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3

lemma blocks3InnerPS_constantCoeff : PowerSeries.constantCoeff blocks3InnerPS = 0 := by
  unfold blocks3InnerPS
  have hX : PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ) = 0 :=
    _root_.PowerSeries.constantCoeff_X
  have hpow2 : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) =
      (PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ)) ^ 2 :=
    _root_.map_pow (PowerSeries.constantCoeff (R := ℂ)) (PowerSeries.X : PowerSeries ℂ) 2
  have hpow2zero : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) = 0 :=
    hpow2.trans ((congrArg (fun z : ℂ => z ^ 2) hX).trans (by norm_num))
  have hsmul2 : PowerSeries.constantCoeff (R := ℂ)
      ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) =
        (2⁻¹ : ℂ) • PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) :=
    _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℂ) ^ 2) (2⁻¹ : ℂ)
  have hsmul2zero : PowerSeries.constantCoeff (R := ℂ)
      ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) = 0 :=
    hsmul2.trans ((congrArg (fun z : ℂ => (2⁻¹ : ℂ) • z) hpow2zero).trans (smul_zero _))
  have hpow3 : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 3) =
      (PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ)) ^ 3 :=
    _root_.map_pow (PowerSeries.constantCoeff (R := ℂ)) (PowerSeries.X : PowerSeries ℂ) 3
  have hpow3zero : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 3) = 0 :=
    hpow3.trans ((congrArg (fun z : ℂ => z ^ 3) hX).trans (by norm_num))
  have hsmul3 : PowerSeries.constantCoeff (R := ℂ)
      ((6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3) =
        (6⁻¹ : ℂ) • PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 3) :=
    _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℂ) ^ 3) (6⁻¹ : ℂ)
  have hsmul3zero : PowerSeries.constantCoeff (R := ℂ)
      ((6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3) = 0 :=
    hsmul3.trans ((congrArg (fun z : ℂ => (6⁻¹ : ℂ) • z) hpow3zero).trans (smul_zero _))
  have hadd2 : (PowerSeries.constantCoeff (R := ℂ)) ((PowerSeries.X : PowerSeries ℂ) + ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)) = (PowerSeries.constantCoeff (R := ℂ)) (PowerSeries.X : PowerSeries ℂ) + (PowerSeries.constantCoeff (R := ℂ)) ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) :=
    _root_.map_add (PowerSeries.constantCoeff (R := ℂ)) (PowerSeries.X : PowerSeries ℂ) ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)
  have hadd2zero : (PowerSeries.constantCoeff (R := ℂ)) ((PowerSeries.X : PowerSeries ℂ) + ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)) = 0 :=
    hadd2.trans ((congrArg₂ (fun x y : ℂ => x + y) hX hsmul2zero).trans (add_zero (0 : ℂ)))
  have hadd3 : (PowerSeries.constantCoeff (R := ℂ)) (((PowerSeries.X : PowerSeries ℂ) + ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)) + ((6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3)) =
      (PowerSeries.constantCoeff (R := ℂ)) ((PowerSeries.X : PowerSeries ℂ) + ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)) + (PowerSeries.constantCoeff (R := ℂ)) ((6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3) :=
    _root_.map_add (PowerSeries.constantCoeff (R := ℂ)) ((PowerSeries.X : PowerSeries ℂ) + ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)) ((6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3)
  exact hadd3.trans
    ((congrArg₂ (fun x y : ℂ => x + y) hadd2zero hsmul3zero).trans (add_zero (0 : ℂ)))

theorem blocks3Carrier_eq_complex_subst :
    blocks3Carrier = (PowerSeries.exp ℂ).subst blocks3InnerPS := by
  rw [blocks3Carrier, AnalyticCombinatorics.Ch1.CombClass.egf_blocks3]
  have hsubst : PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℚ) +
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
          (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    have hX : PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ) = 0 :=
      _root_.PowerSeries.constantCoeff_X
    have hpow2 : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) =
        (PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ)) ^ 2 :=
      _root_.map_pow (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X : PowerSeries ℚ) 2
    have hpow2zero : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) = 0 :=
      hpow2.trans ((congrArg (fun z : ℚ => z ^ 2) hX).trans (by norm_num))
    have hsmul2 : PowerSeries.constantCoeff (R := ℚ)
        ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) =
          (2⁻¹ : ℚ) • PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) :=
      _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℚ) ^ 2) (2⁻¹ : ℚ)
    have hsmul2zero : PowerSeries.constantCoeff (R := ℚ)
        ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) = 0 :=
      hsmul2.trans ((congrArg (fun z : ℚ => (2⁻¹ : ℚ) • z) hpow2zero).trans (smul_zero _))
    have hpow3 : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 3) =
        (PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ)) ^ 3 :=
      _root_.map_pow (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X : PowerSeries ℚ) 3
    have hpow3zero : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 3) = 0 :=
      hpow3.trans ((congrArg (fun z : ℚ => z ^ 3) hX).trans (by norm_num))
    have hsmul3 : PowerSeries.constantCoeff (R := ℚ)
        ((6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3) =
          (6⁻¹ : ℚ) • PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 3) :=
      _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℚ) ^ 3) (6⁻¹ : ℚ)
    have hsmul3zero : PowerSeries.constantCoeff (R := ℚ)
        ((6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3) = 0 :=
      hsmul3.trans ((congrArg (fun z : ℚ => (6⁻¹ : ℚ) • z) hpow3zero).trans (smul_zero _))
    have hadd2 : (PowerSeries.constantCoeff (R := ℚ)) ((PowerSeries.X : PowerSeries ℚ) + ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)) = (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X : PowerSeries ℚ) + (PowerSeries.constantCoeff (R := ℚ)) ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) :=
      _root_.map_add (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X : PowerSeries ℚ) ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)
    have hadd2zero : (PowerSeries.constantCoeff (R := ℚ)) ((PowerSeries.X : PowerSeries ℚ) + ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)) = 0 :=
      hadd2.trans ((congrArg₂ (fun x y : ℚ => x + y) hX hsmul2zero).trans (add_zero (0 : ℚ)))
    have hadd3 : (PowerSeries.constantCoeff (R := ℚ)) (((PowerSeries.X : PowerSeries ℚ) + ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)) + ((6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3)) =
        (PowerSeries.constantCoeff (R := ℚ)) ((PowerSeries.X : PowerSeries ℚ) + ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)) + (PowerSeries.constantCoeff (R := ℚ)) ((6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3) :=
      _root_.map_add (PowerSeries.constantCoeff (R := ℚ)) ((PowerSeries.X : PowerSeries ℚ) + ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)) ((6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3)
    exact hadd3.trans
      ((congrArg₂ (fun x y : ℚ => x + y) hadd2zero hsmul3zero).trans (add_zero (0 : ℚ)))
  have hmap_inner :
      (((PowerSeries.X : PowerSeries ℚ) +
          (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
            (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3).map
          (algebraMap ℚ ℂ)) =
        blocks3InnerPS := by
    ext n
    by_cases h1 : n = 1
    · subst n
      norm_num [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
      change (1 : ℂ) = ((1 : ℂ) + 0) + 0
      exact ((add_zero ((1 : ℂ) + 0)).trans (add_zero (1 : ℂ))).symm
    by_cases h2 : n = 2
    · subst n
      norm_num [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
      change (0 : ℂ) = (0 : ℂ)
      rfl
    by_cases h3 : n = 3
    · subst n
      norm_num [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
      change (0 : ℂ) = (0 : ℂ)
      rfl
    simp [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow, h2, h3,
      add_assoc]
  have hmap_exp :
      (PowerSeries.exp ℚ).map (algebraMap ℚ ℂ) = PowerSeries.exp ℂ := by
    ext n
    simp
  change (((PowerSeries.exp ℚ).subst
        ((PowerSeries.X : PowerSeries ℚ) +
          (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
            (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3)).map
      (algebraMap ℚ ℂ)) = _
  rw [PowerSeries.map_subst
    (a := ((PowerSeries.X : PowerSeries ℚ) +
      (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
        (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3))
    (h := algebraMap ℚ ℂ) hsubst (PowerSeries.exp ℚ)]
  rw [hmap_exp]
  change (PowerSeries.exp ℂ).subst
      ((((PowerSeries.X : PowerSeries ℚ) +
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
          (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3).map
          (algebraMap ℚ ℂ))) =
    (PowerSeries.exp ℂ).subst blocks3InnerPS
  rw [hmap_inner]

lemma blocks3Inner_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => z + z ^ 2 / 2 + z ^ 3 / 6)
      (PowerSeries.toFMLS blocks3InnerPS) (0 : ℂ) := by
  have hX : HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) :=
    InvolutionHAdmissible.hasFPowerSeriesAt_id_toFMLS_X
  have hX2 : HasFPowerSeriesAt (fun z : ℂ => z * z)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using InvolutionHAdmissible.hasFPowerSeriesAt_mul_toFMLS hX hX
  have hX3 : HasFPowerSeriesAt (fun z : ℂ => (z * z) * z)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 3)) (0 : ℂ) := by
    have hmul := InvolutionHAdmissible.hasFPowerSeriesAt_mul_toFMLS hX2 hX
    simpa [pow_succ, pow_two, mul_assoc] using hmul
  have hhalf : HasFPowerSeriesAt (fun z : ℂ => (2⁻¹ : ℂ) • (z * z))
      ((2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2))
      (0 : ℂ) := by
    simpa using (HasFPowerSeriesAt.const_smul (c := (2⁻¹ : ℂ)) hX2)
  have hsixth : HasFPowerSeriesAt (fun z : ℂ => (6⁻¹ : ℂ) • ((z * z) * z))
      ((6⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 3))
      (0 : ℂ) := by
    simpa using (HasFPowerSeriesAt.const_smul (c := (6⁻¹ : ℂ)) hX3)
  have hsum := (hX.add hhalf).add hsixth
  have hseries :
      PowerSeries.toFMLS blocks3InnerPS =
        PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ) +
          (2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2) +
            (6⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 3) := by
    ext n
    simp [blocks3InnerPS, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]
  rw [hseries]
  convert hsum using 1
  funext z
  simp [smul_eq_mul]
  ring_nf

lemma blocks3Fun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt blocks3Fun blocks3Series (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS (PowerSeries.exp ℂ))
      ((fun z : ℂ => z + z ^ 2 / 2 + z ^ 3 / 6) 0) := by
    simpa using ExpStirling.expCarrier_hasFPowerSeriesAt_zero
  have hcomp := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := fun z : ℂ => z + z ^ 2 / 2 + z ^ 3 / 6)
    houter blocks3Inner_hasFPowerSeriesAt_zero
  change HasFPowerSeriesAt blocks3Fun (PowerSeries.toFMLS blocks3Carrier) (0 : ℂ)
  rw [blocks3Carrier_eq_complex_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp blocks3InnerPS_constantCoeff]
  simpa [Function.comp_def, blocks3Fun, blocks3Series] using hcomp

/-- Hayman window for the cubic polynomial saddle. -/
def blocks3SaddleDeltaReal (r : ℝ) : ℝ :=
  r ^ (-(7 / 6 : ℝ))

@[simp] lemma blocks3SaddleAReal_apply (r : ℝ) :
    blocks3SaddleAReal r = r + r ^ 2 + r ^ 3 / 2 := rfl

@[simp] lemma blocks3SaddleBReal_apply (r : ℝ) :
    blocks3SaddleBReal r = r + 2 * r ^ 2 + 3 * r ^ 3 / 2 := rfl

@[simp] lemma blocks3SaddleDeltaReal_apply (r : ℝ) :
    blocks3SaddleDeltaReal r = r ^ (-(7 / 6 : ℝ)) := rfl

/-- The exact exponent left after removing the linear and quadratic saddle terms. -/
def blocks3LocalExponent (r θ : ℝ) : ℂ :=
  (r : ℂ) * ExpStirling.expLocalRemainder θ +
    (((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ)) +
      (((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))

lemma complex_two_mul_theta_I (θ : ℝ) :
    (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
      ((2 * θ : ℝ) : ℂ) * Complex.I := by
  simp [Complex.ofReal_mul, mul_assoc, mul_comm]

lemma complex_three_mul_theta_I (θ : ℝ) :
    (((3 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
      ((3 * θ : ℝ) : ℂ) * Complex.I := by
  simp [Complex.ofReal_mul, mul_assoc, mul_comm]

lemma blocks3_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r θ =
      Complex.exp (blocks3LocalExponent r θ) := by
  unfold saddleLocalRatio blocks3Fun blocks3LocalExponent blocks3SaddleAReal blocks3SaddleBReal
  have hsq_full :
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 =
        ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by norm_num]
    rw [show (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
        ((2 * θ : ℝ) : ℂ) * Complex.I by
      simpa using complex_two_mul_theta_I θ]
  have hcube_full :
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3 =
        ((r ^ 3 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [show (r : ℂ) ^ 3 = ((r ^ 3 : ℝ) : ℂ) by norm_num]
    rw [show (((3 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
        ((3 * θ : ℝ) : ℂ) * Complex.I by
      simpa using complex_three_mul_theta_I θ]
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  rw [ExpStirling.expLocalRemainder_eq θ]
  rw [ExpStirling.expLocalRemainder_eq (2 * θ)]
  rw [ExpStirling.expLocalRemainder_eq (3 * θ)]
  rw [hsq_full, hcube_full]
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow]
  ring_nf

lemma blocks3_f_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < (blocks3Fun (r : ℂ)).re := by
  refine Eventually.of_forall fun r => ?_
  unfold blocks3Fun
  have harg :
      (r : ℂ) + (r : ℂ) ^ 2 / 2 + (r : ℂ) ^ 3 / 6 =
        ((r + r ^ 2 / 2 + r ^ 3 / 6 : ℝ) : ℂ) := by
    norm_num
  have hval :
      Complex.exp (((r + r ^ 2 / 2 + r ^ 3 / 6 : ℝ) : ℂ)) =
        ((Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) : ℝ) : ℂ) := by
    simp
  rw [harg, hval]
  exact Real.exp_pos (r + r ^ 2 / 2 + r ^ 3 / 6)

lemma blocks3_b_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < blocks3SaddleBReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold blocks3SaddleBReal
  positivity

lemma blocks3_delta_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < blocks3SaddleDeltaReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold blocks3SaddleDeltaReal
  exact Real.rpow_pos_of_pos hr _

lemma blocks3_delta_tendsto_zero :
    Tendsto blocks3SaddleDeltaReal atTop (𝓝 0) := by
  simpa [blocks3SaddleDeltaReal] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6))

lemma blocks3_delta_le_pi_eventually :
    ∀ᶠ r : ℝ in atTop, blocks3SaddleDeltaReal r ≤ Real.pi :=
  blocks3_delta_tendsto_zero.eventually_le_const Real.pi_pos

lemma blocks3_delta_le_one_eventually :
    ∀ᶠ r : ℝ in atTop, blocks3SaddleDeltaReal r ≤ 1 :=
  blocks3_delta_tendsto_zero.eventually_le_const zero_lt_one

lemma blocks3_delta_mul_rpow_three_halves_eventually :
    (fun r : ℝ => blocks3SaddleDeltaReal r * r ^ (3 / 2 : ℝ)) =ᶠ[atTop]
      fun r : ℝ => r ^ (1 / 3 : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  calc
    blocks3SaddleDeltaReal r * r ^ (3 / 2 : ℝ)
        = r ^ (-(7 / 6 : ℝ)) * r ^ (3 / 2 : ℝ) := by
          simp [blocks3SaddleDeltaReal]
    _ = r ^ (-(7 / 6 : ℝ) + (3 / 2 : ℝ)) := by
          rw [Real.rpow_add hr]
    _ = r ^ (1 / 3 : ℝ) := by norm_num

lemma blocks3_delta_sqrt_b_tendsto_atTop :
    Tendsto (fun r : ℝ => blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))
      atTop atTop := by
  have hpow : Tendsto (fun r : ℝ => r ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    blocks3_delta_mul_rpow_three_halves_eventually] with r hr heq
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hb_ge : r ^ 3 ≤ blocks3SaddleBReal r := by
    unfold blocks3SaddleBReal
    nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) hr0]
  have hrpow_sq : (r ^ (3 / 2 : ℝ)) ^ 2 = r ^ 3 := by
    calc
      (r ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = r ^ ((3 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hr0 (3 / 2 : ℝ) 2).symm
      _ = r ^ (3 : ℝ) :=
        congrArg (fun e : ℝ => r ^ e) (by norm_num : (3 / 2 : ℝ) * 2 = 3)
      _ = r ^ (3 : ℕ) := Real.rpow_natCast r 3
  have hsqrt_ge : r ^ (3 / 2 : ℝ) ≤ Real.sqrt (blocks3SaddleBReal r) := by
    exact Real.le_sqrt_of_sq_le (by simpa [hrpow_sq] using hb_ge)
  have hδ_nonneg : 0 ≤ blocks3SaddleDeltaReal r := by
    unfold blocks3SaddleDeltaReal
    positivity
  calc
    r ^ (1 / 3 : ℝ) =
        blocks3SaddleDeltaReal r * r ^ (3 / 2 : ℝ) := heq.symm
    _ ≤ blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r) :=
      mul_le_mul_of_nonneg_left hsqrt_ge hδ_nonneg

lemma blocks3_differentiableOn_eventually :
    ∀ᶠ r : ℝ in atTop,
      DifferentiableOn ℂ blocks3Fun (Metric.closedBall (0 : ℂ) r) := by
  refine Eventually.of_forall fun r => ?_
  unfold blocks3Fun
  fun_prop

def blocks3LocalControl (r : ℝ) : ℝ :=
  r ^ 3 * (blocks3SaddleDeltaReal r) ^ 3

lemma blocks3LocalControl_eq_rpow_eventually :
    blocks3LocalControl =ᶠ[atTop] fun r : ℝ => r ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hr0 : 0 ≤ r := hr.le
  have hr3_rpow : r ^ 3 = r ^ (3 : ℝ) := by
    exact (Real.rpow_natCast r 3).symm
  have hdelta_pow :
      (r ^ (-(7 / 6 : ℝ))) ^ 3 = r ^ (-(7 / 6 : ℝ) * (3 : ℝ)) :=
    (Real.rpow_mul_natCast hr0 (-(7 / 6 : ℝ)) 3).symm
  unfold blocks3LocalControl blocks3SaddleDeltaReal
  calc
    r ^ 3 * (r ^ (-(7 / 6 : ℝ))) ^ 3
        = r ^ (3 : ℝ) * r ^ (-(7 / 6 : ℝ) * (3 : ℝ)) := by
          rw [hr3_rpow, hdelta_pow]
    _ = r ^ ((3 : ℝ) + (-(7 / 6 : ℝ) * (3 : ℝ))) := by
          rw [Real.rpow_add hr]
    _ = r ^ (-(1 / 2 : ℝ)) := by norm_num

lemma blocks3LocalControl_tendsto_zero :
    Tendsto blocks3LocalControl atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  exact Tendsto.congr' blocks3LocalControl_eq_rpow_eventually.symm hpow

def blocks3LocalConstant : ℝ :=
  100 * Real.exp 3

lemma blocks3LocalBound_tendsto_zero :
    Tendsto (fun r : ℝ => blocks3LocalConstant * blocks3LocalControl r) atTop (𝓝 0) := by
  simpa using blocks3LocalControl_tendsto_zero.const_mul blocks3LocalConstant

lemma expLocalRemainder_norm_le_exp_three {θ : ℝ} (hθ : |θ| ≤ 3) :
    ‖ExpStirling.expLocalRemainder θ‖ ≤ Real.exp 3 * |θ| ^ 3 := by
  calc
    ‖ExpStirling.expLocalRemainder θ‖ ≤ |θ| ^ 3 * Real.exp |θ| :=
      ExpStirling.expLocalRemainder_norm_le θ
    _ ≤ |θ| ^ 3 * Real.exp 3 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 3)
    _ = Real.exp 3 * |θ| ^ 3 := by ring

lemma blocks3_local_exponent_norm_le_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ θ : ℝ, |θ| ≤ blocks3SaddleDeltaReal r →
      ‖blocks3LocalExponent r θ‖ ≤ blocks3LocalConstant * blocks3LocalControl r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3_delta_le_one_eventually] with
    r hr hδ_le_one θ hθδ
  let δ : ℝ := blocks3SaddleDeltaReal r
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, blocks3SaddleDeltaReal]
    positivity
  have hθ_one : |θ| ≤ 1 := hθδ.trans hδ_le_one
  have hθ_three : |θ| ≤ 3 := hθ_one.trans (by norm_num)
  have h2θ_three : |2 * θ| ≤ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hθ_one]
  have h3θ_three : |3 * θ| ≤ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hθ_one]
  have hθ3δ3 : |θ| ^ 3 ≤ δ ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg θ) hθδ 3
  have h2θ3 : |2 * θ| ^ 3 ≤ 8 * δ ^ 3 := by
    calc
      |2 * θ| ^ 3 = 8 * |θ| ^ 3 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf
      _ ≤ 8 * δ ^ 3 := mul_le_mul_of_nonneg_left hθ3δ3 (by norm_num)
  have h3θ3 : |3 * θ| ^ 3 ≤ 27 * δ ^ 3 := by
    calc
      |3 * θ| ^ 3 = 27 * |θ| ^ 3 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        ring_nf
      _ ≤ 27 * δ ^ 3 := mul_le_mul_of_nonneg_left hθ3δ3 (by norm_num)
  have hrem1 := expLocalRemainder_norm_le_exp_three hθ_three
  have hrem2 := expLocalRemainder_norm_le_exp_three h2θ_three
  have hrem3 := expLocalRemainder_norm_le_exp_three h3θ_three
  have hterm1 :
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ ≤
        Real.exp 3 * (r * δ ^ 3) := by
    calc
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖
          = r * ‖ExpStirling.expLocalRemainder θ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (Real.exp 3 * |θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem1 hr0
      _ ≤ r * (Real.exp 3 * δ ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθ3δ3 (Real.exp_pos 3).le) hr0
      _ = Real.exp 3 * (r * δ ^ 3) := by ring_nf
  have hterm2 :
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ ≤
        4 * Real.exp 3 * (r ^ 2 * δ ^ 3) := by
    have hcoef0 : 0 ≤ r ^ 2 / 2 := by positivity
    calc
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖
          = (r ^ 2 / 2) * ‖ExpStirling.expLocalRemainder (2 * θ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef0]
      _ ≤ (r ^ 2 / 2) * (Real.exp 3 * |2 * θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem2 hcoef0
      _ ≤ (r ^ 2 / 2) * (Real.exp 3 * (8 * δ ^ 3)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2θ3 (Real.exp_pos 3).le) hcoef0
      _ = 4 * Real.exp 3 * (r ^ 2 * δ ^ 3) := by
        have hcoeff : (2 : ℝ)⁻¹ * 8 = 4 := by norm_num
        calc
          (r ^ 2 / 2) * (Real.exp 3 * (8 * δ ^ 3)) =
              ((2 : ℝ)⁻¹ * 8) * (Real.exp 3 * (r ^ 2 * δ ^ 3)) := by
            rw [div_eq_mul_inv]
            ac_rfl
          _ = 4 * Real.exp 3 * (r ^ 2 * δ ^ 3) := by
            rw [hcoeff]
            exact (mul_assoc (4 : ℝ) (Real.exp 3) (r ^ 2 * δ ^ 3)).symm
  have hterm3 :
      ‖(((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))‖ ≤
        (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) := by
    have hcoef0 : 0 ≤ r ^ 3 / 6 := by positivity
    calc
      ‖(((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))‖
          = (r ^ 3 / 6) * ‖ExpStirling.expLocalRemainder (3 * θ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef0]
      _ ≤ (r ^ 3 / 6) * (Real.exp 3 * |3 * θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem3 hcoef0
      _ ≤ (r ^ 3 / 6) * (Real.exp 3 * (27 * δ ^ 3)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h3θ3 (Real.exp_pos 3).le) hcoef0
      _ = (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) := by ring_nf
  have hterm1' :
      Real.exp 3 * (r * δ ^ 3) ≤ Real.exp 3 * (r ^ 3 * δ ^ 3) := by
    have one_le_r2 : 1 ≤ r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
    have hr_le_r3 : r ≤ r ^ 3 := by
      calc
        r = r * 1 := by ring
        _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left one_le_r2 hr0
        _ = r ^ 3 := by ring
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hr_le_r3 (pow_nonneg hδ0 3)) (Real.exp_pos 3).le
  have hterm2' :
      4 * Real.exp 3 * (r ^ 2 * δ ^ 3) ≤
        4 * Real.exp 3 * (r ^ 3 * δ ^ 3) := by
    have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by
      calc
        r ^ 2 = r ^ 2 * 1 := by ring
        _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
        _ = r ^ 3 := by ring
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hr2_le_r3 (pow_nonneg hδ0 3))
      (by positivity)
  calc
    ‖blocks3LocalExponent r θ‖
        ≤ ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ +
          ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ +
            ‖(((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))‖ := by
        let A : ℂ := (r : ℂ) * ExpStirling.expLocalRemainder θ
        let B : ℂ := (((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))
        let C : ℂ := (((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))
        change ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖
        calc
          ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
          _ ≤ (‖A‖ + ‖B‖) + ‖C‖ :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right (norm_add_le A B) ‖C‖
          _ = ‖A‖ + ‖B‖ + ‖C‖ := by ring
    _ ≤ Real.exp 3 * (r * δ ^ 3) +
          4 * Real.exp 3 * (r ^ 2 * δ ^ 3) +
            (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) :=
        add_le_add (add_le_add hterm1 hterm2) hterm3
    _ ≤ Real.exp 3 * (r ^ 3 * δ ^ 3) +
          4 * Real.exp 3 * (r ^ 3 * δ ^ 3) +
            (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) :=
        add_le_add (add_le_add hterm1' hterm2') (le_refl _)
    _ ≤ blocks3LocalConstant * blocks3LocalControl r := by
      unfold blocks3LocalConstant blocks3LocalControl
      dsimp [δ]
      have hnonneg : 0 ≤ r ^ 3 * (r ^ (-(7 / 6 : ℝ))) ^ 3 := by
        positivity
      nlinarith [Real.exp_pos 3, hnonneg]

lemma blocks3_local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in atTop, ∀ θ : ℝ,
      |θ| ≤ blocks3SaddleDeltaReal r →
        ‖saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r θ - 1‖ ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ r : ℝ in atTop, blocks3LocalConstant * blocks3LocalControl r ≤ ε / 2 :=
    blocks3LocalBound_tendsto_zero.eventually_le_const hhalf
  have hone :
      ∀ᶠ r : ℝ in atTop, blocks3LocalConstant * blocks3LocalControl r ≤ 1 :=
    blocks3LocalBound_tendsto_zero.eventually_le_const zero_lt_one
  filter_upwards [blocks3_local_exponent_norm_le_eventually, hsmall, hone] with
    r hloc hsmallr honer θ hθ
  rw [blocks3_saddleLocalRatio_eq]
  have hz : ‖blocks3LocalExponent r θ‖ ≤ blocks3LocalConstant * blocks3LocalControl r :=
    hloc θ hθ
  have hz_one : ‖blocks3LocalExponent r θ‖ ≤ 1 := hz.trans honer
  calc
    ‖Complex.exp (blocks3LocalExponent r θ) - 1‖
        ≤ 2 * ‖blocks3LocalExponent r θ‖ :=
          Complex.norm_exp_sub_one_le hz_one
    _ ≤ 2 * (blocks3LocalConstant * blocks3LocalControl r) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    _ ≤ ε := by linarith

lemma blocks3_saddleGAt_norm (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt blocks3Fun r n θ‖ =
      Real.exp (r * (Real.cos θ - 1) +
        (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
          (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)) := by
  unfold saddleGAt blocks3Fun
  have hphase : ‖Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hden :
      ‖Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2 + (r : ℂ) ^ 3 / 6)‖ =
        Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) := by
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.add_re, Complex.add_re]
    have hsq : (((r : ℂ) ^ 2 / 2).re = r ^ 2 / 2) := by
      rw [Complex.div_re]
      have hre : ((r : ℂ) ^ 2).re = r ^ 2 := by
        rw [pow_two, Complex.mul_re]
        simp
        ring
      have him : ((r : ℂ) ^ 2).im = 0 := by
        rw [pow_two, Complex.mul_im]
        simp
      rw [hre, him]
      norm_num [Complex.normSq]
      ring
    have hcube : (((r : ℂ) ^ 3 / 6).re = r ^ 3 / 6) := by
      rw [Complex.div_re]
      have hre : ((r : ℂ) ^ 3).re = r ^ 3 := by
        rw [pow_succ, pow_two, Complex.mul_re]
        simp
        ring
      have him : ((r : ℂ) ^ 3).im = 0 := by
        rw [pow_succ, pow_two, Complex.mul_im]
        simp
      rw [hre, him]
      norm_num [Complex.normSq]
      ring
    rw [hsq, hcube]
    simp
  have hnum_re :
      (((r : ℂ) * Complex.exp (θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 / 2 +
            ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 3 / 6).re =
        r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) +
          (r ^ 3 / 6) * Real.cos (3 * θ) := by
    have hsq_div :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 / 2 =
          (((r ^ 2 / 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I)) := by
      have hsq0 :
          ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 =
            ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) := by
        rw [mul_pow, ← Complex.exp_nat_mul]
        rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by norm_num]
        rw [show (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
            ((2 * θ : ℝ) : ℂ) * Complex.I by
          simpa using complex_two_mul_theta_I θ]
      rw [hsq0]
      norm_num [Complex.ofReal_mul]
      ring_nf
    have hcube_div :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3 / 6 =
          (((r ^ 3 / 6 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I)) := by
      have hcube0 :
          ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3 =
            ((r ^ 3 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I) := by
        rw [mul_pow, ← Complex.exp_nat_mul]
        rw [show (r : ℂ) ^ 3 = ((r ^ 3 : ℝ) : ℂ) by norm_num]
        rw [show (((3 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
            ((3 * θ : ℝ) : ℂ) * Complex.I by
          simpa using complex_three_mul_theta_I θ]
      rw [hcube0]
      norm_num [Complex.ofReal_mul]
      ring_nf
    rw [hsq_div, hcube_div]
    have hre1 :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re = r * Real.cos θ := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    have hre2 :
        ((((r ^ 2 / 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I)).re =
          (r ^ 2 / 2) * Real.cos (2 * θ)) := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    have hre3 :
        ((((r ^ 3 / 6 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I)).re =
          (r ^ 3 / 6) * Real.cos (3 * θ)) := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.add_re, Complex.add_re, hre1, hre2, hre3]
  have hnum :
      ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2 +
            ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 3 / 6)‖ =
        Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) +
          (r ^ 3 / 6) * Real.cos (3 * θ)) := by
    rw [Complex.norm_exp, hnum_re]
  have hden_pos : 0 < Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) := Real.exp_pos _
  calc
    ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2 +
            ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 3 / 6) /
        Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2 + (r : ℂ) ^ 3 / 6) *
        Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖
        = Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) +
              (r ^ 3 / 6) * Real.cos (3 * θ)) /
            Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) := by
          rw [norm_mul, hphase, mul_one, norm_div, hnum, hden]
    _ = Real.exp (r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)) := by
      rw [← Real.exp_sub]
      congr 1
      ring_nf

def blocks3TailE (r : ℝ) : ℝ :=
  Real.exp (-(1 / (2 * Real.pi ^ 2)) * r ^ (2 / 3 : ℝ))

lemma blocks3TailE_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ blocks3TailE r :=
  Eventually.of_forall fun r => by
    unfold blocks3TailE
    positivity

lemma blocks3TailE_decay :
    Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r)
      atTop (𝓝 0) := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (9 / 4 : ℝ) * Real.exp (-c * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (9 / 4 : ℝ) c hc
  have hy : Tendsto (fun r : ℝ => r ^ (2 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)
  have hcomp :
      Tendsto (fun r : ℝ => (r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) *
        Real.exp (-c * r ^ (2 / 3 : ℝ))) atTop (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto (fun r : ℝ => Real.sqrt (10 * Real.pi) *
        ((r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) *
          Real.exp (-c * r ^ (2 / 3 : ℝ)))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (10 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · exact Eventually.of_forall fun r => by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have one_le_r2 : 1 ≤ r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
    have hr_le_r3 : r ≤ r ^ 3 := by
      calc
        r = r * 1 := by ring
        _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left one_le_r2 hr0
        _ = r ^ 3 := by ring
    have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by
      calc
        r ^ 2 = r ^ 2 * 1 := by ring
        _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
        _ = r ^ 3 := by ring
    have hB_le : blocks3SaddleBReal r ≤ 5 * r ^ 3 := by
      unfold blocks3SaddleBReal
      nlinarith
    have hsqrt :
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) ≤
          Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ) := by
      have hmul : 2 * Real.pi * blocks3SaddleBReal r ≤ 10 * Real.pi * r ^ 3 := by
        calc
          2 * Real.pi * blocks3SaddleBReal r
              ≤ 2 * Real.pi * (5 * r ^ 3) :=
                mul_le_mul_of_nonneg_left hB_le (by positivity)
          _ = 10 * Real.pi * r ^ 3 := by ring_nf
      calc
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r)
            ≤ Real.sqrt (10 * Real.pi * r ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ) := by
          have h10pi : 0 ≤ 10 * Real.pi := by positivity
          rw [Real.sqrt_mul h10pi (r ^ 3)]
          rw [Real.sqrt_eq_rpow (r ^ 3)]
          have hpow : (r ^ 3) ^ (1 / 2 : ℝ) = r ^ (3 / 2 : ℝ) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hr0]
            norm_num
          rw [hpow]
    have hrpow : (r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) = r ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_mul hr0]
      norm_num
    calc
      Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r
          ≤ (Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ)) * blocks3TailE r :=
            mul_le_mul_of_nonneg_right hsqrt (by
              unfold blocks3TailE
              positivity)
      _ = Real.sqrt (10 * Real.pi) *
            ((r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) *
              Real.exp (-c * r ^ (2 / 3 : ℝ))) := by
        unfold blocks3TailE
        dsimp [c]
        rw [hrpow]
        ring_nf

lemma blocks3_tail_bound_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
      blocks3SaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt blocks3Fun r n θ‖ ≤ blocks3TailE r := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hc_le_three : c ≤ 3 / Real.pi ^ 2 := by
    dsimp [c]
    field_simp [Real.pi_ne_zero]
    norm_num
  have hc_le_two_ninths : c ≤ 2 / 9 := by
    dsimp [c]
    have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.two_le_pi]
    have hden : 0 < 2 * Real.pi ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr n θ hδθ hθπ
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ blocks3SaddleDeltaReal r := by
    unfold blocks3SaddleDeltaReal
    positivity
  rw [blocks3_saddleGAt_norm]
  unfold blocks3TailE
  apply Real.exp_le_exp.mpr
  by_cases hsmall : |θ| ≤ Real.pi / 3
  · have h3θπ : |3 * θ| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      nlinarith
    have hcos3 := Real.cos_le_one_sub_mul_cos_sq h3θπ
    have hcos3_sub : Real.cos (3 * θ) - 1 ≤
        -(2 / Real.pi ^ 2) * (3 * θ) ^ 2 := by
      linarith
    have htail_scale :
        r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2 = r ^ (2 / 3 : ℝ) := by
      have hr3_rpow : r ^ 3 = r ^ (3 : ℝ) := by
        exact (Real.rpow_natCast r 3).symm
      have hdelta_pow :
          (r ^ (-(7 / 6 : ℝ))) ^ 2 = r ^ (-(7 / 6 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hr0 (-(7 / 6 : ℝ)) 2).symm
      unfold blocks3SaddleDeltaReal
      calc
        r ^ 3 * (r ^ (-(7 / 6 : ℝ))) ^ 2
            = r ^ (3 : ℝ) * r ^ (-(7 / 6 : ℝ) * (2 : ℝ)) := by
              rw [hr3_rpow, hdelta_pow]
        _ = r ^ ((3 : ℝ) + (-(7 / 6 : ℝ) * (2 : ℝ))) := by
              rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hr)]
        _ = r ^ (2 / 3 : ℝ) := by norm_num
    have hθsq : (blocks3SaddleDeltaReal r) ^ 2 ≤ θ ^ 2 := by
      calc
        (blocks3SaddleDeltaReal r) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ hδ0 hδθ 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hmain :
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
          ≤ -c * r ^ (2 / 3 : ℝ) := by
      have hcos1_nonpos : Real.cos θ - 1 ≤ 0 := by
        linarith [Real.cos_le_one θ]
      have hcos2_nonpos : Real.cos (2 * θ) - 1 ≤ 0 := by
        linarith [Real.cos_le_one (2 * θ)]
      have hleft_nonpos : r * (Real.cos θ - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hr0 hcos1_nonpos
      have hmiddle_nonpos : (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos2_nonpos
      have hcoef_nonpos : -(3 / Real.pi ^ 2) ≤ 0 := by
        have hpos : 0 ≤ 3 / Real.pi ^ 2 := by positivity
        linarith
      have hstrong :
          (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
            ≤ -(3 / Real.pi ^ 2) * (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2) := by
        calc
          (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
              ≤ (r ^ 3 / 6) * (-(2 / Real.pi ^ 2) * (3 * θ) ^ 2) :=
                mul_le_mul_of_nonneg_left hcos3_sub (by positivity)
          _ = -(3 / Real.pi ^ 2) * (r ^ 3 * θ ^ 2) := by ring_nf
          _ ≤ -(3 / Real.pi ^ 2) *
                (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2) := by
            exact mul_le_mul_of_nonpos_left
              (mul_le_mul_of_nonneg_left hθsq (by positivity)) hcoef_nonpos
      have hconst : c * r ^ (2 / 3 : ℝ) ≤
          (3 / Real.pi ^ 2) * (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2) := by
        rw [htail_scale]
        exact mul_le_mul_of_nonneg_right hc_le_three (Real.rpow_nonneg hr0 _)
      calc
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
            ≤ 0 + 0 +
                (-(3 / Real.pi ^ 2) *
                  (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2)) :=
              add_le_add (add_le_add hleft_nonpos hmiddle_nonpos) hstrong
        _ ≤ -c * r ^ (2 / 3 : ℝ) := by linarith
    exact hmain
  · have hlarge : Real.pi / 3 < |θ| := lt_of_not_ge hsmall
    have hcos1 := Real.cos_le_one_sub_mul_cos_sq hθπ
    have hcos1_sub : Real.cos θ - 1 ≤ -(2 / Real.pi ^ 2) * θ ^ 2 := by
      linarith
    have hθsq_lower : (Real.pi / 3) ^ 2 ≤ θ ^ 2 := by
      calc
        (Real.pi / 3) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hlarge.le 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hmain :
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
          ≤ -c * r ^ (2 / 3 : ℝ) := by
      have hcos2_nonpos : Real.cos (2 * θ) - 1 ≤ 0 := by
        linarith [Real.cos_le_one (2 * θ)]
      have hcos3_nonpos : Real.cos (3 * θ) - 1 ≤ 0 := by
        linarith [Real.cos_le_one (3 * θ)]
      have hmiddle_nonpos : (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos2_nonpos
      have hright_nonpos : (r ^ 3 / 6) * (Real.cos (3 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos3_nonpos
      have hcoef_nonpos : -(2 / Real.pi ^ 2) ≤ 0 := by
        have hpos : 0 ≤ 2 / Real.pi ^ 2 := by positivity
        linarith
      have hfirst :
          r * (Real.cos θ - 1) ≤ -(2 / 9) * r := by
        calc
          r * (Real.cos θ - 1)
              ≤ r * (-(2 / Real.pi ^ 2) * θ ^ 2) :=
                mul_le_mul_of_nonneg_left hcos1_sub hr0
          _ ≤ r * (-(2 / Real.pi ^ 2) * (Real.pi / 3) ^ 2) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonpos_left hθsq_lower hcoef_nonpos) hr0
          _ = -(2 / 9) * r := by
            field_simp [Real.pi_ne_zero]
            ring
      have hpow_le : r ^ (2 / 3 : ℝ) ≤ r := by
        calc
          r ^ (2 / 3 : ℝ) ≤ r ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (2 / 3 : ℝ) ≤ 1)
          _ = r := by rw [Real.rpow_one]
      have hconst : c * r ^ (2 / 3 : ℝ) ≤ (2 / 9) * r := by
        calc
          c * r ^ (2 / 3 : ℝ) ≤ (2 / 9) * r ^ (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right hc_le_two_ninths (Real.rpow_nonneg hr0 _)
          _ ≤ (2 / 9) * r :=
            mul_le_mul_of_nonneg_left hpow_le (by norm_num)
      calc
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
            ≤ -(2 / 9) * r + 0 + 0 :=
              add_le_add (add_le_add hfirst hmiddle_nonpos) hright_nonpos
        _ ≤ -c * r ^ (2 / 3 : ℝ) := by linarith
    exact hmain

lemma blocks3_tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in atTop, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * E r)
        atTop (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        blocks3SaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt blocks3Fun r n θ‖ ≤ E r) := by
  exact ⟨blocks3TailE, blocks3TailE_nonneg_eventually, blocks3TailE_decay,
    blocks3_tail_bound_eventually⟩

lemma blocks3SaddleAReal_strictMonoOn_nonneg :
    StrictMonoOn blocks3SaddleAReal (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  unfold blocks3SaddleAReal
  have hdiff : 0 < y - x := sub_pos.mpr hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hquad_nonneg : 0 ≤ (x ^ 2 + x * y + y ^ 2) / 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, hxy0]
  have hfactor : 0 < 1 + x + y + (x ^ 2 + x * y + y ^ 2) / 2 := by
    linarith
  have hpos : 0 < (y - x) *
      (1 + x + y + (x ^ 2 + x * y + y ^ 2) / 2) :=
    mul_pos hdiff hfactor
  nlinarith

lemma blocks3SaddleRadius_nonneg (n : ℕ) : 0 ≤ blocks3SaddleRadius n :=
  (Classical.choose_spec
    (blocks3SaddleAReal_exists_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))).1

lemma blocks3SaddleAReal_radius (n : ℕ) :
    blocks3SaddleAReal (blocks3SaddleRadius n) = (n : ℝ) :=
  (Classical.choose_spec
    (blocks3SaddleAReal_exists_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))).2

lemma blocks3SaddleRadius_tendsto_atTop :
    Tendsto blocks3SaddleRadius atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  let M0 : ℝ := max M 0
  obtain ⟨N, hN⟩ := exists_nat_gt (blocks3SaddleAReal M0)
  refine ⟨N, fun n hn => ?_⟩
  have hM0_nonneg : 0 ≤ M0 := le_max_right _ _
  have hM_le_M0 : M ≤ M0 := le_max_left _ _
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hAM0_lt_n : blocks3SaddleAReal M0 < (n : ℝ) := hN.trans_le hnR
  by_contra hnot
  have hr_lt_M : blocks3SaddleRadius n < M := lt_of_not_ge hnot
  have hr_lt_M0 : blocks3SaddleRadius n < M0 := hr_lt_M.trans_le hM_le_M0
  have hstrict :
      blocks3SaddleAReal (blocks3SaddleRadius n) < blocks3SaddleAReal M0 :=
    blocks3SaddleAReal_strictMonoOn_nonneg
      (blocks3SaddleRadius_nonneg n) hM0_nonneg hr_lt_M0
  rw [blocks3SaddleAReal_radius] at hstrict
  linarith

def blocks3HAdmissible : HAdmissible blocks3Fun blocks3Series where
  ρ := blocks3Series.radius
  radFilter := atTop
  a := blocks3SaddleAReal
  b := blocks3SaddleBReal
  δ := blocks3SaddleDeltaReal
  hp := blocks3Fun_hasFPowerSeriesAt_zero
  radius_eq := rfl
  radius_pos := by
    simpa [blocks3Series] using blocks3Fun_hasFPowerSeriesAt_zero.radius_pos
  rad_neBot := by infer_instance
  r_pos := eventually_gt_atTop (0 : ℝ)
  differentiableOn := blocks3_differentiableOn_eventually
  f_pos := blocks3_f_pos_eventually
  b_pos := blocks3_b_pos_eventually
  δ_pos := blocks3_delta_pos_eventually
  δ_le_pi := blocks3_delta_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := blocks3_delta_sqrt_b_tendsto_atTop
  local_uniform := blocks3_local_uniform
  tail_uniform := blocks3_tail_uniform

def blocks3HAdmissibleSaddleSequence : SaddleSequence blocks3HAdmissible where
  r := blocks3SaddleRadius
  tendsTo := by
    simpa [blocks3HAdmissible] using blocks3SaddleRadius_tendsto_atTop
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      change blocks3SaddleAReal (blocks3SaddleRadius n) = (n : ℝ)
      exact blocks3SaddleAReal_radius n

theorem blocks3_coeff_isEquivalent_saddle_from_HAdmissible :
    (fun n : ℕ => blocks3Series.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale blocks3Fun blocks3SaddleRadius
        (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n) := by
  have h := coeff_isEquivalent_saddle blocks3HAdmissible blocks3HAdmissibleSaddleSequence
  simpa [HAdmissible.B, blocks3HAdmissibleSaddleSequence, blocks3HAdmissible] using h

theorem blocks3_count_over_factorial_isEquivalent_saddle :
    (fun n : ℕ =>
      (((AnalyticCombinatorics.Ch1.CombClass.blocks3.counts n : ℝ) / n.factorial : ℝ) : ℂ))
      ~[atTop]
      (fun n : ℕ => saddleScale blocks3Fun blocks3SaddleRadius
        (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n) := by
  simpa [blocks3Series, PowerSeries.coeff_toFMLS, blocks3Carrier_coeff, blocks3CoeffR] using
    blocks3_coeff_isEquivalent_saddle_from_HAdmissible

end Blocks3HAdmissible
end
end

/-!
# Set partitions into blocks of size ≤ 3: the Moser–Wyman real saddle asymptotic

`blocks3_count_over_factorial_isEquivalent_saddle` (Blocks3HAdmissible) gives the abstract H-admissible
saddle estimate for the number of set partitions of `[n]` into blocks of size 1, 2, or 3 (EGF
`exp(z + z²/2 + z³/6)`).  This file realifies the abstract scale to the Moser–Wyman formula

  `B₃(n) / n! ~ exp(r_n + r_n²/2 + r_n³/6) / ( r_n^n · √(2π · (r_n + 2r_n² + 3r_n³/2)) )`,
  `r_n + r_n² + r_n³/2 = n`.

"Unfold and realify" of `saddleScale`, mirroring `BellRealSaddle` / `InvolutionRealSaddle`.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology Real

namespace Blocks3HAdmissible

/-- The saddle radius is strictly positive for `n ≥ 1`. -/
lemma blocks3SaddleRadius_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < blocks3SaddleRadius n := by
  have hrnn : 0 ≤ blocks3SaddleRadius n := blocks3SaddleRadius_nonneg n
  have hA : blocks3SaddleAReal (blocks3SaddleRadius n) = (n : ℝ) := blocks3SaddleAReal_radius n
  rcases hrnn.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at hA
    simp only [blocks3SaddleAReal] at hA
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← hA] at hnR
    simp at hnR

/-- The variance factor at the saddle is positive for `n ≥ 1`. -/
lemma blocks3SaddleBReal_radius_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < blocks3SaddleBReal (blocks3SaddleRadius n) := by
  have hr : 0 < blocks3SaddleRadius n := blocks3SaddleRadius_pos_of_pos hn
  unfold blocks3SaddleBReal
  positivity

/-- The blocks-≤3 EGF is real on real input. -/
lemma blocks3Fun_real_on_real (r : ℝ) :
    blocks3Fun (r : ℂ) = (Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) : ℂ) := by
  unfold blocks3Fun
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **Realification** of the abstract saddle scale (`n ≥ 1`). -/
lemma blocks3_saddleScale_eq_ofReal_real_saddle {n : ℕ} (hn : 0 < n) :
    saddleScale blocks3Fun blocks3SaddleRadius
        (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n
      = (blocks3RealSaddleScale n : ℂ) := by
  have hr : 0 < blocks3SaddleRadius n := blocks3SaddleRadius_pos_of_pos hn
  have hB : 0 < blocks3SaddleBReal (blocks3SaddleRadius n) := blocks3SaddleBReal_radius_pos_of_pos hn
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * blocks3SaddleBReal (blocks3SaddleRadius n)) :=
    Real.sqrt_pos.mpr (by positivity)
  unfold blocks3RealSaddleScale saddleScale saddlePref saddlePrefAt
  rw [blocks3Fun_real_on_real]
  have hrC : ((blocks3SaddleRadius n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsqrtC :
      ((Real.sqrt (2 * Real.pi * blocks3SaddleBReal (blocks3SaddleRadius n)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt.ne'
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

/-- Eventual equality of the abstract complex scale and the real scale. -/
lemma blocks3_saddleScale_eventually_eq_ofReal_real_saddle :
    (fun n : ℕ =>
      saddleScale blocks3Fun blocks3SaddleRadius
        (fun n => blocks3SaddleBReal (blocks3SaddleRadius n)) n)
      =ᶠ[atTop] (fun n : ℕ => (blocks3RealSaddleScale n : ℂ)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact blocks3_saddleScale_eq_ofReal_real_saddle (by omega : 0 < n)

end Blocks3HAdmissible
end

open Blocks3HAdmissible
open Filter Asymptotics
open scoped Topology Real
theorem solution :
    (fun n : ℕ => blocks3CoeffR n) ~[atTop] blocks3RealSaddleScale := by
  rw [← ofReal_isEquivalent_iff]
  exact blocks3_count_over_factorial_isEquivalent_saddle.congr_right
    blocks3_saddleScale_eventually_eq_ofReal_real_saddle
