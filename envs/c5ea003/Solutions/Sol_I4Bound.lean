-- Prove2me | solution 1 for I4Bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T18:44:49.00986+00:00
-- url     : https://prove2.me/submissions/f8569327-c655-47d1-9ce9-742e749e640e

import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_MediumPNT_defs
import Definitions.Def_MellinCalculus_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs
import Theorems.Thm_MellinOfSmooth1b

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open Chebyshev

open ComplexConjugate

open MeasureTheory

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

--open scoped ArithmeticFunction in

-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED

theorem solution {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by

  have reOne : re 1 = 1 := rfl
  have imOne : im 1 = 0 := rfl
  have reThree : re 3 = 3 := rfl
  have imThree : im 3 = 0 := rfl

  unfold I₄ SmoothedChebyshevIntegrand

  let S : Set ℝ := (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1
  let C' : ℝ := sSup S
  have bddAboveS : BddAbove S := by
    refine IsCompact.bddAbove ?_
    unfold S
    refine IsCompact.image_of_continuousOn ?_ ?_
    · exact isCompact_Icc
    · refine ContinuousOn.norm ?_
      have : (fun (t : ℝ) ↦ -ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        (fun (t : ℝ) ↦ -(ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by
        apply funext
        intro x
        apply neg_div
      rw[this]
      refine ContinuousOn.neg ?_
      have : (fun (t : ℝ) ↦ ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        ((ζ' / ζ) ∘ (fun (t : ℝ) ↦ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := rfl
      rw[this]
      apply h_logDeriv_holo.continuousOn.comp' (by fun_prop)
      unfold MapsTo
      intro x xInIcc
      simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, mem_diff, mem_singleton_iff]
      have : ¬↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I = 1 := by
        by_contra h
        rw[Complex.ext_iff, sub_re, add_re, sub_im, add_im] at h
        repeat rw[mul_im] at h
        repeat rw[mul_re] at h
        rw[sub_im, sub_re, reOne, imOne, reThree, imThree, I_im, I_re] at h
        repeat rw[ofReal_re] at h
        repeat rw[ofReal_im] at h
        ring_nf at h
        obtain ⟨_, ripGoal⟩ := h
        linarith
      refine ⟨?_, this⟩
      rw [mem_reProdIm]
      simp only [sub_re, add_re, ofReal_re, mul_re, one_re, ofReal_im, sub_im, one_im, sub_self,
        mul_zero, sub_zero, re_ofNat, I_re, im_ofNat, I_im, mul_one, add_im, mul_im, zero_mul,
        add_zero, zero_sub, mem_Icc, le_refl, neg_le_self_iff, Nat.ofNat_nonneg, and_self, and_true]
      rw [Set.uIcc_of_le]
      · rw [mem_Icc]
        constructor
        · simp only [le_add_iff_nonneg_right]
          apply mul_nonneg
          · exact xInIcc.1
          · linarith [hσ₂.2]
        · have : σ₂ + x * (1 - σ₂) = σ₂ * (1 - x) + x := by ring
          rw [this]
          clear this
          have : (2 : ℝ) = 1 * 1 + 1 := by norm_num
          rw [this]
          clear this
          gcongr
          · linarith [xInIcc.2]
          · exact hσ₂.2.le
          · linarith [xInIcc.1]
          · exact xInIcc.2
      · linarith [hσ₂.2]

  have CPrimeNonneg : 0 ≤ C' := by
    apply Real.sSup_nonneg
    intro x x_in_S
    obtain ⟨t, ht, rfl⟩ := x_in_S
    exact NNReal.coe_nonneg _

  obtain ⟨D, Dpos, MellinSmooth1bBound⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  let C : ℝ := C' * D / sInf ((fun t => ‖ σ₂ + (t : ℝ) * (1 - σ₂) - 3 * I ‖₊ ^ 2) '' Set.Icc 0 1)
  use C
  have sInfPos : 0 < sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1) := by
    refine (IsCompact.lt_sInf_iff_of_continuous ?_ ?_ ?_ 0).mpr ?_
    · exact isCompact_Icc
    · exact Nonempty.of_subtype
    · have : (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) =
        (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ * ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) := by
        apply funext
        intro x
        rw[pow_two]
      rw[this]
      have : ContinuousOn (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) (Icc 0 1) := by
        refine ContinuousOn.nnnorm ?_
        refine ContinuousOn.sub ?_ (by exact continuousOn_const)
        refine ContinuousOn.add (by exact continuousOn_const) ?_
        exact ContinuousOn.mul (by exact Complex.continuous_ofReal.continuousOn) (by exact continuousOn_const)
      exact ContinuousOn.mul (by exact this) (by exact this)
    · intro x xLoc
      apply pow_pos
      have temp : |(↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I).im| ≤
        ‖↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I‖₊ := by apply Complex.abs_im_le_norm
      rw[sub_im, add_im, mul_im, mul_im, I_re, I_im, sub_im, sub_re] at temp
      repeat rw[ofReal_re] at temp
      repeat rw[ofReal_im] at temp
      rw[reThree, imOne] at temp
      ring_nf at temp ⊢
      rw[(by ring : σ₂ - σ₂ * x + x - I * 3 = σ₂ - σ₂ * x + (x - I * 3))] at temp ⊢
      rw[abs_of_neg, neg_neg] at temp
      · have : (3 : NNReal) ≤ ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ := temp
        positivity
      · rw[neg_lt_zero]
        norm_num
  have CNonneg : 0 ≤ C := by
    unfold C
    apply mul_nonneg
    · exact mul_nonneg (by exact CPrimeNonneg) (by exact Dpos.le)
    · rw[inv_nonneg]
      norm_cast
      convert sInfPos.le using 5
      norm_cast
  use CNonneg

  let Tlb : ℝ := max 4 (max (rexp (A ^ (9 : ℝ)⁻¹)) (rexp ((A / (1 - σ₂)) ^ (9 : ℝ)⁻¹)))
  use Tlb

  have : 3 < Tlb := by
    unfold Tlb
    rw[lt_max_iff]
    refine Or.inl ?_
    norm_num
  use this

  intro X X_gt_three ε ε_pos ε_lt_one T T_gt_Tlb σ₁
  have σ₂_le_σ₁ : σ₂ ≤ σ₁ := by
    have logTlb_pos : 0 < Real.log Tlb := by
      rw[← Real.log_one]
      exact log_lt_log (by norm_num) (by linarith)
    have logTlb_nonneg : 0 ≤ Real.log Tlb := le_of_lt (by exact logTlb_pos)
    have expr_nonneg : 0 ≤ A / (1 - σ₂) := by
      apply div_nonneg
      · linarith [hA.1]
      · rw[sub_nonneg]
        exact le_of_lt hσ₂.2
    have temp : σ₂ ≤ 1 - A / Real.log Tlb ^ 9 := by
      have : rexp ((A / (1 - σ₂)) ^ (9 : ℝ)⁻¹) ≤ Tlb := by
        unfold Tlb
        nth_rewrite 2 [max_comm]
        rw[max_left_comm]
        apply le_max_of_le_left (by rfl)
      rw[← Real.le_log_iff_exp_le] at this
      · have h1 : 0 ≤ (A / (1 - σ₂)) ^ (9 : ℝ)⁻¹ := by apply Real.rpow_nonneg (by exact expr_nonneg)
        have h2 : 0 < (9 : ℝ) := Nat.ofNat_pos'
        rw[← Real.rpow_le_rpow_iff h1 logTlb_nonneg h2] at this
        have h: ((A / (1 - σ₂)) ^ (9 : ℝ)⁻¹) ^ (9 : ℝ) = A / (1 - σ₂) := rpow_inv_rpow (by exact expr_nonneg) (by exact Ne.symm (OfNat.zero_ne_ofNat 9))
        rw[h, div_le_iff₀, mul_comm, ← div_le_iff₀] at this
        · have temp : Real.log Tlb ^ (9 : ℕ) = Real.log Tlb ^ (9 : ℝ) := Eq.symm (rpow_ofNat (Real.log Tlb) 9)
          rw[temp]
          linarith
        · exact rpow_pos_of_pos (by exact logTlb_pos) 9
        · rw[sub_pos]
          exact hσ₂.2
      · positivity
    have : 1 - A / Real.log Tlb ^ 9 ≤ 1 - A / Real.log T ^ 9 := by
      apply sub_le_sub (by rfl)
      apply div_le_div₀
      · exact le_of_lt (by exact hA.1)
      · rfl
      · apply pow_pos (by exact logTlb_pos)
      · apply pow_le_pow_left₀ (by exact logTlb_nonneg)
        apply log_le_log (by positivity)
        exact le_of_lt (by exact T_gt_Tlb)
    exact le_trans temp this
  have minσ₂σ₁ : min σ₂ σ₁ = σ₂ := min_eq_left (by exact σ₂_le_σ₁)
  have maxσ₂σ₁ : max σ₂ σ₁ = σ₁ := max_eq_right (by exact σ₂_le_σ₁)
  have σ₁_lt_one : σ₁ < 1 := by
    rw[← sub_zero 1]
    unfold σ₁
    apply sub_lt_sub_left
    apply div_pos (by exact hA.1)
    apply pow_pos
    rw[← Real.log_one]
    exact log_lt_log (by norm_num) (by linarith)

  rw[norm_mul, ← one_mul C]
  have : 1 * C * X * X ^ (-A / Real.log T ^ 9) / ε = 1 * (C * X * X ^ (-A / Real.log T ^ 9) / ε) := by ring
  rw[this]
  apply mul_le_mul
  · rw[norm_div, norm_one]
    repeat rw[norm_mul]
    rw[Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg pi_nonneg, Complex.norm_I, mul_one]
    have : 1 / (2 * π) < 1 / 6 := by
      rw[one_div_lt_one_div]
      · refine (div_lt_iff₀' ?_).mp ?_
        · norm_num
        ring_nf
        refine gt_iff_lt.mpr ?_
        exact Real.pi_gt_three
      · positivity
      · norm_num
    exact le_of_lt (lt_trans this (by norm_num))
  · let f : ℝ → ℂ := fun σ ↦ (-ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I))
    have temp : ‖∫ (σ : ℝ) in σ₂..σ₁, -ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I)‖ ≤
      C * X * X ^ (-A / Real.log T ^ 9) / ε * |σ₁ - σ₂| := by
      have : ∀ x ∈ Set.uIoc σ₂ σ₁, ‖f x‖ ≤ C * X * X ^ (-A / Real.log T ^ 9) / ε := by
        intro x xInIoc
        let t : ℝ := (x - σ₂) / (1 - σ₂)
        have tInIcc : t ∈ Icc 0 1 := by
          unfold t
          constructor
          · apply div_nonneg
            · rw[sub_nonneg]
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact le_of_lt (by exact xInIoc.1)
            · rw[sub_nonneg]
              apply le_of_lt (by exact hσ₂.2)
          · rw[div_le_one]
            · refine sub_le_sub ?_ (by rfl)
              unfold uIoc at xInIoc
              rw[maxσ₂σ₁] at xInIoc
              apply le_trans xInIoc.2
              exact le_of_lt (by exact σ₁_lt_one)
            · rw[sub_pos]
              exact hσ₂.2
        have tExpr : (↑σ₂ + t * (1 - ↑σ₂) - 3 * I) = (↑x - 3 * I) := by
          unfold t
          simp only [ofReal_div, ofReal_sub, ofReal_one, sub_left_inj]
          rw[div_mul_comm, div_self]
          · simp only [one_mul, add_sub_cancel]
          · refine sub_ne_zero_of_ne ?_
            apply Ne.symm
            rw[Complex.ofReal_ne_one]
            exact ne_of_lt (by exact hσ₂.2)
        unfold f
        simp only [Complex.norm_mul]
        have : C * X * X ^ (-A / Real.log T ^ 9) / ε =
          (C / ε) * (X * X ^ (-A / Real.log T ^ 9)) := by ring
        rw[this]
        have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
          C / ε := by
          unfold C
          rw[div_div]
          nth_rewrite 2 [div_eq_mul_inv]
          have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ≤ C' := by
            unfold C'
            have : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ∈
              (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1 := by
              rw[Set.mem_image]
              use t
              constructor
              · exact tInIcc
              · rw[tExpr]
                rfl
            exact le_csSup (by exact bddAboveS) (by exact this)
          have : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)‖ ≤
            D * ((sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)) * ε)⁻¹ := by
            nth_rewrite 3 [mul_comm]
            let s : ℂ := x - 3 * I
            have : 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I) =
              𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s := rfl
            rw[this]
            have temp : σ₂ ≤ s.re := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              apply le_of_lt
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact xInIoc.1
            have : s.re ≤ 2 := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              have : x < 1 := by
                unfold uIoc at xInIoc
                rw[maxσ₂σ₁] at xInIoc
                exact lt_of_le_of_lt xInIoc.2 σ₁_lt_one
              linarith
            have temp : ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹ := by
              exact MellinSmooth1bBound σ₂ hσ₂.1 s temp this ε ε_pos ε_lt_one
            have : D * (ε * ‖s‖ ^ 2)⁻¹ ≤ D * (ε * ↑(sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)))⁻¹ := by
              refine mul_le_mul (by rfl) ?_ ?_ (by exact le_of_lt (by exact Dpos))
              · rw[inv_le_inv₀]
                · apply mul_le_mul (by rfl)
                  · rw[NNReal.coe_sInf]
                    apply csInf_le
                    · apply NNReal.bddBelow_coe
                    · unfold s
                      rw[Set.mem_image]
                      let xNorm : NNReal := ‖x - 3 * I‖₊ ^ 2
                      use xNorm
                      constructor
                      · rw[Set.mem_image]
                        use t
                        exact ⟨tInIcc, by rw[tExpr]⟩
                      · rfl
                  · exact le_of_lt (by exact sInfPos)
                  · exact le_of_lt (by exact ε_pos)
                · apply mul_pos (ε_pos)
                  refine sq_pos_of_pos ?_
                  refine norm_pos_iff.mpr ?_
                  refine ne_zero_of_re_pos ?_
                  unfold s
                  rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
                  ring_nf
                  unfold uIoc at xInIoc
                  rw[minσ₂σ₁] at xInIoc
                  exact lt_trans hσ₂.1 xInIoc.1
                · exact mul_pos (ε_pos) (sInfPos)
              · rw[inv_nonneg]
                apply mul_nonneg (by exact le_of_lt (by exact ε_pos))
                exact sq_nonneg ‖s‖
            exact le_trans temp this
          rw[mul_assoc]
          apply mul_le_mul (by exact temp) (by exact this)
          · have this : 0 ≤ |(𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑x - 3 * I)).re| := by
              apply abs_nonneg
            exact le_trans this (by refine Complex.abs_re_le_norm ?_)
          · exact CPrimeNonneg
        have : ‖(X : ℂ) ^ (↑x - 3 * I)‖ ≤
          X * X ^ (-A / Real.log T ^ 9) := by
          nth_rewrite 2 [← Real.rpow_one X]
          rw[← Real.rpow_add]
          · rw[Complex.norm_cpow_of_ne_zero]
            · rw[sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, reThree, imThree]
              ring_nf
              rw[Complex.norm_of_nonneg]
              · rw[Complex.arg_ofReal_of_nonneg]
                · rw[zero_mul, neg_zero, Real.exp_zero]
                  simp only [inv_one, mul_one, inv_pow]
                  refine rpow_le_rpow_of_exponent_le ?_ ?_
                  · linarith
                  · unfold uIoc at xInIoc
                    rw[maxσ₂σ₁] at xInIoc
                    unfold σ₁ at xInIoc
                    ring_nf at xInIoc ⊢
                    exact xInIoc.2
                · positivity
              · positivity
            · refine ne_zero_of_re_pos ?_
              rw[ofReal_re]
              positivity
          · positivity
        apply mul_le_mul
        · exact temp
        · exact this
        · rw[Complex.norm_cpow_eq_rpow_re_of_pos]
          · rw[sub_re, mul_re, ofReal_re, I_re, I_im, reThree, imThree]
            ring_nf
            apply Real.rpow_nonneg
            positivity
          · positivity
        · exact div_nonneg CNonneg (le_of_lt ε_pos)
      exact intervalIntegral.norm_integral_le_of_norm_le_const this
    have : C * X * X ^ (-A / Real.log T ^ 9) / ε * |σ₁ - σ₂| ≤
      C * X * X ^ (-A / Real.log T ^ 9) / ε := by
      have : |σ₁ - σ₂| ≤ 1 := by
        rw[abs_of_nonneg]
        · rw[← sub_zero 1]
          exact sub_le_sub σ₁_lt_one.le hσ₂.1.le
        · rw[sub_nonneg]
          exact σ₂_le_σ₁
      bound
    exact le_trans temp this
  · simp only [norm_nonneg]
  norm_num

open Filter Topology

-- `x * rexp (-c * (log x) ^ B)) = Real.exp (Real.log x - c * (Real.log x) ^ B))`
-- so if `B < 1`, the exponent goes to infinity

