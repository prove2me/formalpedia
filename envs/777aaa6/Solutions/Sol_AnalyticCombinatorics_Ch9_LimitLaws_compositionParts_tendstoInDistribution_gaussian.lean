-- Prove2me | solution 1 for AnalyticCombinatorics.Ch9.LimitLaws.compositionParts_tendstoInDistribution_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:58:32.74389+00:00
-- url     : https://prove2.me/submissions/477b0fb3-b35d-43b1-a19c-8d3127895b76

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_BinaryWordCLT
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_QuasiPowers
import Definitions.Def_AnalyticCombinatorics_Compatibility_TendstoInDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_CompositionParts
import Theorems.Thm_AnalyticCombinatorics_Ch9_LimitLaws_quasiPowers_tendstoInDistribution_of_continuousAt
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
open Filter MeasureTheory
open scoped Topology

namespace AnalyticCombinatorics.Compatibility

variable {ι E Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [TopologicalSpace E]
  {X Y : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι}

protected lemma TendstoInDistribution.congr [OpensMeasurableSpace E] {T : Ω' → E}
    (hXY : ∀ i, X i =ᵐ[μ i] Y i) (hZT : Z =ᵐ[μ'] T) (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution Y l T μ μ' where
  forall_aemeasurable i := (h.forall_aemeasurable i).congr (hXY i)
  aemeasurable_limit := h.aemeasurable_limit.congr hZT
  tendsto := by
    convert h.tendsto using 2 with n
    · simpa using Measure.map_congr (hXY n).symm
    · rw! [Measure.map_congr hZT]
      rfl

end AnalyticCombinatorics.Compatibility
end

section
/-!
# Quasi-powers and Gaussian limit laws

This file formalizes the Mathlib-supported core of Hwang's quasi-powers theorem.

Mathlib v4.29.0 has Levy's continuity theorem for characteristic functions as
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`, but not a
corresponding Curtiss-style continuity theorem for moment-generating functions.
Accordingly the main limit theorem below takes a logarithmic quasi-powers expansion
on the imaginary axis, proves convergence of normalized characteristic functions,
and then applies Levy's theorem.
-/

noncomputable section

open Asymptotics Complex Filter MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- The real scale identity behind the quasi-powers normalization. -/
lemma quasiPower_scale_sq {β u₂ t : ℝ} (hβ : 0 < β) (hu₂ : 0 < u₂) :
    β * u₂ * ((Real.sqrt (β * u₂))⁻¹ * t) ^ 2 = t ^ 2 := by
  have hsq : (Real.sqrt (β * u₂)) ^ 2 = β * u₂ := by
    rw [Real.sq_sqrt]
    positivity
  have hs_ne : (Real.sqrt (β * u₂) : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos hβ hu₂)
  field_simp [pow_two, hs_ne]
  rw [hsq]

/-- The quadratic term in the normalized quasi-powers exponent tends to the Gaussian exponent. -/
lemma quasiPower_quadratic_term {β u₂ t : ℝ} (hβ : 0 < β) (hu₂ : 0 < u₂) :
    (β : ℂ) * ((u₂ : ℂ) *
        (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)) ^ 2 / 2) =
      - (t : ℂ) ^ 2 / 2 := by
  have hscale := quasiPower_scale_sq (β := β) (u₂ := u₂) (t := t) hβ hu₂
  calc
    (β : ℂ) * ((u₂ : ℂ) *
        (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)) ^ 2 / 2)
        = - (((β * u₂ * ((Real.sqrt (β * u₂))⁻¹ * t) ^ 2 : ℝ) : ℂ)) / 2 := by
          rw [show
            (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)) ^ 2 =
              - ((((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ) ^ 2) by
            rw [pow_two]
            calc
              (Complex.I * ↑((√(β * u₂))⁻¹ * t)) *
                  (Complex.I * ↑((√(β * u₂))⁻¹ * t))
                  = (Complex.I * Complex.I) *
                      (↑((√(β * u₂))⁻¹ * t) * ↑((√(β * u₂))⁻¹ * t)) := by
                    ring
              _ = -↑((√(β * u₂))⁻¹ * t) ^ 2 := by
                    rw [Complex.I_mul_I]
                    ring]
          norm_num
          ring
    _ = - (t : ℂ) ^ 2 / 2 := by
          rw [hscale]
          norm_num

end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

section
/-!
# Binary word counts and the local quasi-powers interface

The one-bit uniform binary-word count has characteristic function zero at `π`.
Consequently it cannot satisfy a global exponential-form `hChar` assumption, whose
right hand side is a complex exponential and therefore never zero.

The binary-word central limit theorem below uses the faithful local interface from
`QuasiPowers.lean`.  We encode bits as signs `-1, 1`; the number of ones in a word is
`(sum of signs + n) / 2`, so the usual count normalization is pointwise equal to the
standardized sign sum.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

set_option backward.isDefEq.respectTransparency false in
/-- Characteristic function of one sign bit. -/
lemma oneBitSignLaw_charFun (s : ℝ) :
    charFun oneBitSignLaw s =
      (Complex.exp (-((s : ℂ) * Complex.I)) + Complex.exp ((s : ℂ) * Complex.I)) / 2 := by
  rw [oneBitSignLaw, charFun_apply_real]
  have hm : Integrable (fun x : ℝ => Complex.exp (s * x * Complex.I))
      (Measure.dirac (-1 : ℝ)) := by
    simpa using
      (integrable_dirac (a := (-1 : ℝ))
        (f := fun x : ℝ => Complex.exp (s * x * Complex.I)) (by simp))
  have hp : Integrable (fun x : ℝ => Complex.exp (s * x * Complex.I))
      (Measure.dirac (1 : ℝ)) := by
    simpa using
      (integrable_dirac (a := (1 : ℝ))
        (f := fun x : ℝ => Complex.exp (s * x * Complex.I)) (by simp))
  rw [integral_smul_measure, integral_add_measure hm hp, integral_dirac, integral_dirac]
  have hto : (ENNReal.ofReal (1 / 2 : ℝ)).toReal = (2 : ℝ)⁻¹ := by
    rw [ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  rw [hto]
  simp
  first
  | ring
  | (push_cast; ring)
  | (simp only [smul_eq_mul, Complex.real_smul]; push_cast; ring)
  | (apply Complex.ext <;> simp <;> ring_nf)

/-- The sign-bit characteristic base. -/
def signBase (z : ℂ) : ℂ :=
  (Complex.exp (-z) + Complex.exp z) / 2

/-- The quadratic quasi-powers main term for a sign bit. -/
def signMain (z : ℂ) : ℂ :=
  z ^ 2 / 2

/-- Exact local logarithmic remainder for sign-coded binary words. -/
def signR (n : ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 0 else
    Complex.log (signBase z ^ n * Complex.exp (-(n : ℂ) * signMain z)) / (n : ℂ)

lemma signSum_charFun (n : ℕ) (s : ℝ) :
    charFun ((P n).map (S n)) s = (signBase (Complex.I * (s : ℂ))) ^ n := by
  change charFun ((Measure.pi fun _ : Fin n => oneBitSignLaw).map (fun p => ∑ i, p i)) s =
    (signBase (Complex.I * (s : ℂ))) ^ n
  have h := congrFun (charFun_map_sum_pi_eq_prod (μ := fun _ : Fin n => oneBitSignLaw)) s
  rw [h]
  simp [oneBitSignLaw_charFun, signBase, Finset.prod_const, Fintype.card_fin, div_pow, mul_comm]

lemma signBase_ne_zero_of_abs_le_half {s : ℝ} (hs : |s| ≤ (1 / 2 : ℝ)) :
    signBase (Complex.I * (s : ℂ)) ≠ 0 := by
  intro hzero
  have hnum : Complex.exp (-(Complex.I * (s : ℂ))) +
      Complex.exp (Complex.I * (s : ℂ)) = 0 := by
    rcases div_eq_zero_iff.mp hzero with h | h
    · exact h
    · norm_num at h
  have hmul := congrArg (fun w : ℂ => w * Complex.exp (Complex.I * (s : ℂ))) hnum
  simp only [add_mul, zero_mul] at hmul
  have hne : Complex.exp (Complex.I * (s : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hexp2 : Complex.exp (2 * (Complex.I * (s : ℂ))) = -1 := by
    rw [Complex.exp_neg, inv_mul_cancel₀ hne] at hmul
    rw [← Complex.exp_add] at hmul
    have harg : Complex.I * (s : ℂ) + Complex.I * (s : ℂ) =
        2 * (Complex.I * (s : ℂ)) := by
      ring
    rw [harg] at hmul
    linear_combination hmul
  have hdiff : Complex.exp (Complex.I * ((2 * s : ℝ) : ℂ)) - 1 = -2 := by
    rw [show Complex.I * ((2 * s : ℝ) : ℂ) = 2 * (Complex.I * (s : ℂ)) by
      norm_num
      ring]
    rw [hexp2]
    norm_num
  have hnorm_eq : ‖Complex.exp (Complex.I * ((2 * s : ℝ) : ℂ)) - 1‖ = 2 := by
    rw [hdiff]
    norm_num
  have hle : ‖Complex.exp (Complex.I * ((2 * s : ℝ) : ℂ)) - 1‖ ≤ ‖2 * s‖ := by
    simpa using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * s))
  have htwo_le_one : (2 : ℝ) ≤ 1 := by
    calc
      (2 : ℝ) = ‖Complex.exp (Complex.I * ((2 * s : ℝ) : ℂ)) - 1‖ := hnorm_eq.symm
      _ ≤ ‖2 * s‖ := hle
      _ = |2 * s| := Real.norm_eq_abs (2 * s)
      _ = 2 * |s| := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (1 / 2 : ℝ) := by gcongr
      _ = 1 := by norm_num
  norm_num at htwo_le_one

lemma sign_hChar : ∃ s₀ > 0, ∀ n s, |s| ≤ s₀ →
    charFun ((P n).map (S n)) s =
      Complex.exp (((n : ℝ) : ℂ) * (((0 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) +
        ((1 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 +
        signR n (Complex.I * (s : ℂ))) + (0 : ℂ)) := by
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro n s hs
  rw [signSum_charFun]
  by_cases hn : n = 0
  · subst n
    simp [signR]
  · let z : ℂ := Complex.I * (s : ℂ)
    let ratio : ℂ := signBase z ^ n * Complex.exp (-(n : ℂ) * signMain z)
    have hbase : signBase z ≠ 0 := signBase_ne_zero_of_abs_le_half (s := s) hs
    have hratio : ratio ≠ 0 := by
      dsimp [ratio]
      exact mul_ne_zero (pow_ne_zero n hbase) (Complex.exp_ne_zero _)
    change signBase z ^ n =
      Complex.exp (((n : ℂ) * ((0 : ℂ) * z + (1 : ℂ) * z ^ 2 / 2 + signR n z) + 0))
    rw [signR, if_neg hn]
    change signBase z ^ n =
      Complex.exp (((n : ℂ) *
        ((0 : ℂ) * z + (1 : ℂ) * z ^ 2 / 2 + Complex.log ratio / (n : ℂ)) + 0))
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [show ((n : ℂ) *
        ((0 : ℂ) * z + (1 : ℂ) * z ^ 2 / 2 + Complex.log ratio / (n : ℂ)) + 0) =
        (n : ℂ) * (z ^ 2 / 2) + Complex.log ratio by
      field_simp [hnC]
      ring]
    change signBase z ^ n = Complex.exp ((n : ℂ) * signMain z + Complex.log ratio)
    rw [Complex.exp_add, Complex.exp_log hratio]
    dsimp [ratio]
    rw [show Complex.exp ((n : ℂ) * signMain z) *
        (signBase z ^ n * Complex.exp (-(n : ℂ) * signMain z)) =
        signBase z ^ n *
          (Complex.exp ((n : ℂ) * signMain z) *
            Complex.exp (-(n : ℂ) * signMain z)) by
      ring]
    rw [← Complex.exp_add]
    rw [show (n : ℂ) * signMain z + (-(n : ℂ) * signMain z) = 0 by ring]
    simp

lemma oneBitSignLaw_charFun_signBase (s : ℝ) :
    charFun oneBitSignLaw s = signBase (Complex.I * (s : ℂ)) := by
  rw [oneBitSignLaw_charFun]
  simp [signBase, mul_comm]

private lemma binaryWordCLT_sin_eq_mul_sinc (x : ℝ) :
    Real.sin x = x * Real.sinc x := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [Real.sinc_of_ne_zero hx]
    field_simp [hx] <;> ring

private lemma binaryWordCLT_cos_two_mul_sub_one (x : ℝ) :
    Real.cos (2 * x) - 1 = -(2 * x ^ 2 * (Real.sinc x) ^ 2) := by
  rw [Real.cos_two_mul', Real.cos_sq', binaryWordCLT_sin_eq_mul_sinc]
  ring

theorem binaryWordCLT_cos_inv_sqrt_pow_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ =>
        ((Complex.exp (-(((√(n : ℝ))⁻¹ * t : ℝ) : ℂ) * Complex.I) +
          Complex.exp ((((√(n : ℝ))⁻¹ * t : ℝ) : ℂ) * Complex.I)) / 2) ^ n)
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  let u : ℕ → ℝ := fun n => (√(n : ℝ))⁻¹ * t / 2
  have hinv :
      Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hu : Tendsto u atTop (𝓝 (0 : ℝ)) := by
    have hs : Tendsto
        (fun n : ℕ => (√(n : ℝ))⁻¹ * (t / 2)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [zero_mul] using hinv.mul_const (t / 2)
    simpa only [u, mul_div_assoc] using hs
  have hsinc :
      Tendsto (fun n : ℕ => Real.sinc (u n)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.sinc_zero] using (Real.continuous_sinc.tendsto 0).comp hu
  have hsq :
      Tendsto (fun n : ℕ => (Real.sinc (u n)) ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_pow] using hsinc.pow 2
  have hlimit :
      Tendsto (fun n : ℕ => -(t ^ 2 / 2) * (Real.sinc (u n)) ^ 2)
        atTop (𝓝 (-(t ^ 2 / 2))) := by
    simpa only [mul_one] using hsq.const_mul (-(t ^ 2 / 2))
  have hquad (n : ℕ) :
      (u n) ^ 2 = (n : ℝ)⁻¹ * t ^ 2 / 4 := by
    dsimp [u]
    rw [div_pow, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  have hfactor (n : ℕ) (hn : n ≠ 0) :
      (n : ℝ) * (u n) ^ 2 = t ^ 2 / 4 := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    calc
      (n : ℝ) * (u n) ^ 2 =
          ((n : ℝ) * (n : ℝ)⁻¹) * t ^ 2 / 4 := by rw [hquad n]; ring
      _ = t ^ 2 / 4 := by rw [mul_inv_cancel₀ hnR, one_mul]
  have htwo (n : ℕ) :
      2 * u n = (√(n : ℝ))⁻¹ * t := by
    dsimp [u]
    ring
  have hrealbase :
      Tendsto (fun n : ℕ =>
        (n : ℝ) * (Real.cos ((√(n : ℝ))⁻¹ * t) - 1))
        atTop (𝓝 (-(t ^ 2 / 2))) := by
    apply hlimit.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    have hpoint :
        (n : ℝ) * (Real.cos ((√(n : ℝ))⁻¹ * t) - 1) =
          -(t ^ 2 / 2) * (Real.sinc (u n)) ^ 2 := by
      calc
        (n : ℝ) * (Real.cos ((√(n : ℝ))⁻¹ * t) - 1) =
            -(2 * ((n : ℝ) * (u n) ^ 2) * (Real.sinc (u n)) ^ 2) := by
          rw [← htwo n, binaryWordCLT_cos_two_mul_sub_one]
          ring
        _ = -(t ^ 2 / 2) * (Real.sinc (u n)) ^ 2 := by
          rw [hfactor n hn0]
          ring
    first
    | exact hpoint
    | exact hpoint.symm
  have hrealpow :
      Tendsto (fun n : ℕ => (Real.cos ((√(n : ℝ))⁻¹ * t)) ^ n)
        atTop (𝓝 (Real.exp (-(t ^ 2 / 2)))) := by
    have hp := Real.tendsto_one_add_pow_exp_of_tendsto hrealbase
    have hfun :
        (fun n : ℕ => (1 + (Real.cos ((√(n : ℝ))⁻¹ * t) - 1)) ^ n) =
        (fun n : ℕ => (Real.cos ((√(n : ℝ))⁻¹ * t)) ^ n) := by
      funext n
      congr 1
      ring
    rw [hfun] at hp
    exact hp
  have hcomplexpow :
      Tendsto (fun n : ℕ => (Real.cos ((√(n : ℝ))⁻¹ * t) : ℂ) ^ n)
        atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
    have hc :
        Tendsto
          (fun n : ℕ => ((Real.cos ((√(n : ℝ))⁻¹ * t) ^ n : ℝ) : ℂ))
          atTop (𝓝 ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hrealpow
    have hend :
        ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) =
          Complex.exp (-(t : ℂ) ^ 2 / 2) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    have hpowers :
        (fun n : ℕ => ((Real.cos ((√(n : ℝ))⁻¹ * t) ^ n : ℝ) : ℂ)) =
        (fun n : ℕ => (Real.cos ((√(n : ℝ))⁻¹ * t) : ℂ) ^ n) := by
      funext n
      norm_cast
    rw [hpowers, hend] at hc
    exact hc
  have hbase (n : ℕ) :
      (Complex.exp (-(((√(n : ℝ))⁻¹ * t : ℝ) : ℂ) * Complex.I) +
        Complex.exp ((((√(n : ℝ))⁻¹ * t : ℝ) : ℂ) * Complex.I)) / 2 =
      (Real.cos ((√(n : ℝ))⁻¹ * t) : ℂ) := by
    rw [Complex.ofReal_cos]
    unfold Complex.cos
    ring
  have hfun :
      (fun n : ℕ =>
        ((Complex.exp (-(((√(n : ℝ))⁻¹ * t : ℝ) : ℂ) * Complex.I) +
          Complex.exp ((((√(n : ℝ))⁻¹ * t : ℝ) : ℂ) * Complex.I)) / 2) ^ n) =
      (fun n : ℕ => (Real.cos ((√(n : ℝ))⁻¹ * t) : ℂ) ^ n) := by
    funext n
    rw [hbase n]
  rw [hfun]
  exact hcomplexpow

lemma signRatio_tendsto_one (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        signBase (qpZ (fun n : ℕ => (n : ℝ)) 1 n t) ^ n *
          Complex.exp (-(n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t)))
      atTop (𝓝 1) := by
  have hclt :
      Tendsto (fun n : ℕ => (charFun oneBitSignLaw ((√n)⁻¹ * t)) ^ n)
        atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
    simpa only [oneBitSignLaw_charFun, neg_mul] using binaryWordCLT_cos_inv_sqrt_pow_tendsto t
  have htarget :
      Tendsto
        (fun n : ℕ => (charFun oneBitSignLaw ((√n)⁻¹ * t)) ^ n *
          Complex.exp ((t : ℂ) ^ 2 / 2)) atTop (𝓝 1) := by
    have hmul := hclt.mul_const (Complex.exp ((t : ℂ) ^ 2 / 2))
    have hlim :
        Complex.exp (-(t : ℂ) ^ 2 / 2) * Complex.exp ((t : ℂ) ^ 2 / 2) = 1 := by
      rw [← Complex.exp_add]
      ring_nf
      simp
    simpa [hlim] using hmul
  refine Tendsto.congr' ?_ htarget
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hbase :
      signBase (qpZ (fun n : ℕ => (n : ℝ)) 1 n t) =
        charFun oneBitSignLaw ((√n)⁻¹ * t) := by
    rw [oneBitSignLaw_charFun_signBase]
    simp [qpZ]
  have hmain :
      (n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t) =
        - (t : ℂ) ^ 2 / 2 := by
    have hquad := quasiPower_quadratic_term (β := (n : ℝ)) (u₂ := 1) (t := t) hnpos
      (by norm_num : (0 : ℝ) < 1)
    simpa [qpZ, signMain] using hquad
  rw [hbase]
  have hnegmain :
      -(n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t) =
        (t : ℂ) ^ 2 / 2 := by
    calc
      -(n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t)
          = -((n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t)) := by ring
      _ = (t : ℂ) ^ 2 / 2 := by
        rw [hmain]
        ring
  rw [hnegmain]

lemma signR_tendsto :
    ∀ t, Tendsto
      (fun n : ℕ =>
        ((n : ℝ) : ℂ) * signR n (qpZ (fun n : ℕ => (n : ℝ)) 1 n t))
      atTop (𝓝 0) := by
  intro t
  have hratio := signRatio_tendsto_one t
  have hlog :
      Tendsto
        (fun n : ℕ => Complex.log
          (signBase (qpZ (fun n : ℕ => (n : ℝ)) 1 n t) ^ n *
            Complex.exp (-(n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t))))
        atTop (𝓝 0) := by
    simpa using hratio.clog (by simp [Complex.slitPlane] : (1 : ℂ) ∈ Complex.slitPlane)
  refine Tendsto.congr' ?_ hlog
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp [signR, hn]
  field_simp [hnC]

lemma normalized_count_eq_sign (n : ℕ) (ω : Ω n) :
    (X n ω - (n : ℝ) * (1 / 2)) / Real.sqrt ((n : ℝ) * (1 / 4)) =
      (S n ω - (n : ℝ) * 0) / Real.sqrt ((n : ℝ) * 1) := by
  by_cases hn : n = 0
  · subst n
    simp [X, S]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hnpos
    have hsqrt :
        Real.sqrt ((n : ℝ) * (1 / 4)) = Real.sqrt (n : ℝ) / 2 := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (n : ℝ)) (1 / 4 : ℝ)]
      norm_num
      ring
    rw [X, hsqrt]
    field_simp [hsqrt_ne]
    ring

end LimitLaws
end Ch9
end AnalyticCombinatorics
end
end

/-!
# Number of parts in a random composition

For `n ≥ 1`, a composition of `n` with `k` parts is equivalently a choice of
`k - 1` of the `n - 1` interior gaps.  Thus the part count has the same law as
`1 + Binomial(n - 1, 1 / 2)`.

The central limit theorem is proved by reusing the local quasi-powers
instantiation for binary words from `BinaryWordCLT.lean`, shifted from `n` to
`n - 1` and then translated by the deterministic `+1`.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- The quasi-powers size parameter for compositions, namely `n - 1`. -/
def compositionBeta (n : ℕ) : ℝ :=
  ((n - 1 : ℕ) : ℝ)

/-- Sum of sign-coded selected gaps. -/
def compositionSignSum (n : ℕ) (ω : CompositionGapΩ n) : ℝ :=
  S (n - 1) ω

/-- The shifted logarithmic remainder inherited from binary words. -/
def compositionSignR (n : ℕ) (z : ℂ) : ℂ :=
  signR (n - 1) z

lemma compositionBeta_tendsto_atTop :
    Tendsto compositionBeta atTop atTop := by
  simpa [compositionBeta] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_sub_atTop_nat 1)

lemma composition_sign_hChar : ∃ s₀ > 0, ∀ n s, |s| ≤ s₀ →
    charFun ((compositionGapP n).map (compositionSignSum n)) s =
      Complex.exp ((compositionBeta n : ℂ) * (((0 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) +
        ((1 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 +
        compositionSignR n (Complex.I * (s : ℂ))) + (0 : ℂ)) := by
  obtain ⟨s₀, hs₀, hlocal⟩ := sign_hChar
  refine ⟨s₀, hs₀, ?_⟩
  intro n s hs
  simpa [compositionGapP, compositionSignSum, compositionBeta, compositionSignR] using
    hlocal (n - 1) s hs

lemma compositionSignR_tendsto :
    ∀ t, Tendsto
      (fun n : ℕ =>
        (compositionBeta n : ℂ) *
          compositionSignR n (qpZ compositionBeta 1 n t))
      atTop (𝓝 0) := by
  intro t
  simpa [compositionBeta, compositionSignR, qpZ] using
    (signR_tendsto t).comp (tendsto_sub_atTop_nat 1)

theorem composition_signSum_tendstoInDistribution_gaussian :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n ω =>
        (compositionSignSum n ω - compositionBeta n * 0) /
          Real.sqrt (compositionBeta n * 1)) atTop
      (fun x : ℝ => x) compositionGapP (gaussianReal 0 1) :=
  quasiPowers_tendstoInDistribution_of_continuousAt
    (P := compositionGapP) (X := compositionSignSum)
    (β := compositionBeta) (u₁ := 0) (u₂ := 1)
    (R := compositionSignR) (V := fun _ : ℂ => 0)
    (by
      intro n
      unfold compositionSignSum
      exact Finset.aemeasurable_fun_sum _ fun i _ => (measurable_pi_apply i).aemeasurable)
    compositionBeta_tendsto_atTop
    (by norm_num)
    continuousAt_const
    rfl
    composition_sign_hChar
    compositionSignR_tendsto

lemma normalized_compositionParts_eq_sign (n : ℕ) (ω : CompositionGapΩ n) :
    (compositionParts n ω - ((n : ℝ) + 1) / 2) /
        Real.sqrt (((n - 1 : ℕ) : ℝ) / 4) =
      (compositionSignSum n ω - compositionBeta n * 0) /
        Real.sqrt (compositionBeta n * 1) := by
  by_cases hn : n = 0
  · subst n
    simp [compositionParts, compositionGapCount, compositionSignSum, compositionBeta, X, S]
  · have hn_real : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      have hn_nat : n = (n - 1) + 1 := by omega
      rw [hn_nat]
      norm_num
    have hcenter :
        ((n : ℝ) + 1) / 2 =
          1 + ((n - 1 : ℕ) : ℝ) * (1 / 2) := by
      rw [hn_real]
      ring
    rw [show compositionParts n ω - ((n : ℝ) + 1) / 2 =
        X (n - 1) ω - ((n - 1 : ℕ) : ℝ) * (1 / 2) by
      simp [compositionParts, compositionGapCount, hcenter]
      ]
    rw [show Real.sqrt (((n - 1 : ℕ) : ℝ) / 4) =
        Real.sqrt (((n - 1 : ℕ) : ℝ) * (1 / 4)) by ring_nf]
    simpa [compositionSignSum, compositionBeta] using normalized_count_eq_sign (n - 1) ω

end LimitLaws
end Ch9
end AnalyticCombinatorics
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch9 AnalyticCombinatorics.Ch9.LimitLaws
open Complex Filter MeasureTheory ProbabilityTheory
open scoped Topology
theorem solution :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n ω =>
        (compositionParts n ω - ((n : ℝ) + 1) / 2) /
          Real.sqrt (((n - 1 : ℕ) : ℝ) / 4)) atTop
      (fun x : ℝ => x) compositionGapP (gaussianReal 0 1) := by
  refine AnalyticCombinatorics.Compatibility.TendstoInDistribution.congr ?_ (ae_of_all _ fun _ => rfl)
    composition_signSum_tendstoInDistribution_gaussian
  intro n
  exact ae_of_all _ fun ω => (normalized_compositionParts_eq_sign n ω).symm
