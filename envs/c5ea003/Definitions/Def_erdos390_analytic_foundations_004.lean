-- Prove2me | Definitions.Def_erdos390_analytic_foundations_004
-- name    : erdos390_analytic_foundations_004
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T14:51:21.655777+00:00
-- url     : https://prove2.me/theorems/9bd33ec3-75cc-4fb3-8ed2-5e59a4f1e59f
-- title:
--   Gauge graph operators, compensated scores and prime-power error ledgers
-- statement:
--   This bundle defines weighted finite graph operators and their gauge spaces, arithmetic and continuum cell operators, normalized quadrature kernels, regression and compensated coefficient norms, finite-mixture tilts, and the prime-power covariance remainder ledgers.
--
--   For a finite band set, edge weights $e_{ij}$ and vertex weights $\omega_i$, the graph operator and weighted gauge are
--   $$(L_eq)_i=\sum_je_{ij}(q_i-q_j),\qquad G_\omega=\left\{q:\sum_i\omega_iq_i=0\right\}.$$
--   When the total weight is nonzero, weighted centering subtracts $\bar q_\omega=(\sum_i\omega_iq_i)/(\sum_i\omega_i)$. The bundle also defines discrete and continuum sharp operators, their row residuals and changes between raw and scaled gauge coordinates.
--
--   On the probability side, compensated scores remove band or nuisance regression components. Valuation tilts and the $JI$, $IJ$, $JJ$ and diagonal tail ledgers separate prime-power contributions from squarefree covariance. Transfer-bound structures name the quantitative bounds required later; inverse constructions take the relevant hypotheses or equivalences as inputs. These objects support the comparison of the finite arithmetic covariance operator with its continuum reference.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FiniteGraphQuotientInverse.lean; grouped definitions extracted from multiple source modules at this commit, including Erdos390.Full.PoissonDickmanDirichlet, Erdos390.Full.PoissonDickmanWeightedInverse, Erdos390.Full.FiniteGraphQuotientInverse, with the remaining originating modules identified by source-module comments in the definition body.

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003


/- Source module: Erdos390.Full.PoissonDickmanDirichlet -/
section


/-!
# A Dirichlet-form route for the Poisson--Dickman covariance kernel

This file isolates the deterministic part of the proposed kernel argument.
For a test function written as `f(t) = t * q(t)`, the covariance quadratic
form is exactly a symmetric Dirichlet energy.  The identity uses only the
Dickman averaging equation already proved in `ConditionedPoissonLimit`; it
does not use a conditional probability measure on the zero-probability
fibre.

The file also closes the sign of the Dirichlet kernel from the delay equation.
It formalizes the classical first-failure proof that the negative logarithmic
derivative of the Dickman function is strictly increasing on the required
range, turns this into the four-point log-concavity inequality, and hence
proves strict negativity of the covariance kernel in the open square.
-/

open Set
open scoped Interval

noncomputable section

namespace Erdos390.Full.PoissonDickmanDirichlet

open MeasureTheory
open DickmanBasic ConditionedPoissonLimit

/-! ## Dickman log-concavity from a first-failure argument -/

/-- The negative logarithmic derivative dictated by the Dickman delay
equation.  On the positive range it is `-rho' / rho`. -/
def dickmanLogSlope (u : ℝ) : ℝ :=
  rho (u - 1) / (u * rho u)

/-- The right-hand side in the differential recurrence for the logarithmic
slope.  On `(2,5)` this is literally `dickmanLogSlope'`.  Keeping it as a
continuous algebraic expression lets the compact first-failure argument
include the endpoint `u = 2` without assigning an endpoint derivative. -/
def slopeGrowth (u : ℝ) : ℝ :=
  dickmanLogSlope u *
    (dickmanLogSlope u - dickmanLogSlope (u - 1) - 1 / u)

lemma dickmanLogSlope_pos {u : ℝ} (hu2 : 2 ≤ u) (hu5 : u ≤ 5) :
    0 < dickmanLogSlope u := by
  unfold dickmanLogSlope
  exact div_pos
    (rho_pos_on_zero_five (by linarith) (by linarith))
    (mul_pos (by linarith) (rho_pos_on_zero_five (by linarith) hu5))

/-- Exact differential recurrence for the Dickman logarithmic slope.  Thus
strict log-concavity is equivalent to proving that the final parenthesis is
positive.  This identity is an unconditional step toward the first-failure
argument; it does not assume monotonicity of the slope. -/
lemma hasDerivAt_dickmanLogSlope {u : ℝ} (hu2 : 2 < u) (hu5 : u < 5) :
    HasDerivAt dickmanLogSlope
      (dickmanLogSlope u *
        (dickmanLogSlope u - dickmanLogSlope (u - 1) - 1 / u)) u := by
  have hu1 : 1 < u := by linarith
  have hu6 : u ≤ 6 := by linarith
  have hum1 : 1 < u - 1 := by linarith
  have hum1_le6 : u - 1 ≤ 6 := by linarith
  have hshift : HasDerivAt (fun x : ℝ => x - 1) 1 u := by
    simpa using (hasDerivAt_id u).sub_const 1
  have hnum : HasDerivAt (fun x : ℝ => rho (x - 1))
      (-rho (u - 2) / (u - 1)) u := by
    have h := (hasDerivAt_rho hum1 hum1_le6).comp u hshift
    simp only [Function.comp_def] at h
    ring_nf at h ⊢
    exact h
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hden : HasDerivAt (fun x : ℝ => x * rho x)
      (rho u + u * (-rho (u - 1) / u)) u := by
    simpa [id] using (hasDerivAt_id u).mul (hasDerivAt_rho hu1 hu6)
  have hru : 0 < rho u := rho_pos_on_zero_five (by linarith) hu5.le
  have hrum1 : 0 < rho (u - 1) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hrum2 : 0 < rho (u - 2) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hum10 : u - 1 ≠ 0 := ne_of_gt (by linarith)
  have hden0 : u * rho u ≠ 0 := mul_ne_zero hu0 (ne_of_gt hru)
  have hraw := hnum.div hden hden0
  apply hraw.congr_deriv
  unfold dickmanLogSlope
  field_simp [hu0, hum10, ne_of_gt hru, ne_of_gt hrum1, ne_of_gt hrum2]
  ring

lemma continuousOn_slopeGrowth_Icc :
    ContinuousOn slopeGrowth (Icc (2 : ℝ) (9 / 2 : ℝ)) := by
  unfold slopeGrowth dickmanLogSlope
  apply ContinuousOn.mul
  · apply ContinuousOn.div
    · exact (continuous_rho.comp
        (continuous_id.sub continuous_const)).continuousOn
    · exact (continuous_id.mul continuous_rho).continuousOn
    · intro x hx
      exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
        (ne_of_gt (rho_pos_on_zero_five (by linarith [hx.1])
          (by norm_num at hx ⊢; linarith [hx.2])))
  · apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · apply ContinuousOn.div
        · exact (continuous_rho.comp
            (continuous_id.sub continuous_const)).continuousOn
        · exact (continuous_id.mul continuous_rho).continuousOn
        · intro x hx
          exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
            (ne_of_gt (rho_pos_on_zero_five (by linarith [hx.1])
              (by norm_num at hx ⊢; linarith [hx.2])))
      · apply ContinuousOn.div
        · exact (continuous_rho.comp
            ((continuous_id.sub continuous_const).sub continuous_const)).continuousOn
        · exact ((continuous_id.sub continuous_const).mul
            (continuous_rho.comp
              (continuous_id.sub continuous_const))).continuousOn
        · intro x hx
          exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
            (ne_of_gt (rho_pos_on_zero_five (by linarith [hx.1])
              (by norm_num at hx ⊢; linarith [hx.2])))
    · exact continuous_const.continuousOn.div continuous_id.continuousOn
        (fun x hx => ne_of_gt (by linarith [hx.1]))

/-- The unit piece of the delay integral.  This is the exact finite-interval
identity used below; in particular, no differentiation under an integral
sign is needed in the first-failure step. -/
lemma rho_delay_unitIntegral {u : ℝ} (hu2 : 2 ≤ u) (hu5 : u ≤ 5) :
    (∫ t in (0 : ℝ)..1, rho (u - t - 1) / (u - t)) =
      rho (u - 1) - rho u := by
  let g : ℝ → ℝ := fun x => rho (x - 1) / x
  have hcont : ContinuousOn g (Icc (1 : ℝ) u) := by
    apply ContinuousOn.div
    · exact (continuous_rho.comp
        (continuous_id.sub continuous_const)).continuousOn
    · exact continuous_id.continuousOn
    · intro x hx
      exact ne_of_gt (by linarith [hx.1])
  have hsub₁ : Icc (1 : ℝ) (u - 1) ⊆ Icc (1 : ℝ) u := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hsub₂ : Icc (u - 1) u ⊆ Icc (1 : ℝ) u := by
    intro x hx
    exact ⟨by linarith [hx.1, hu2], hx.2⟩
  have hg₁ : IntervalIntegrable g volume (1 : ℝ) (u - 1) := by
    have hc := hcont.mono hsub₁
    rw [← uIcc_of_le (by linarith [hu2])] at hc
    exact hc.intervalIntegrable
  have hg₂ : IntervalIntegrable g volume (u - 1) u := by
    have hc := hcont.mono hsub₂
    rw [← uIcc_of_le (by linarith)] at hc
    exact hc.intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals hg₁ hg₂
  have hu := rho_integral_eq (x := u) (by linarith [hu2]) hu5
  have hum := rho_integral_eq (x := u - 1)
    (by linarith [hu2]) (by linarith [hu5])
  have hpiece : (∫ x in (u - 1)..u, g x) = rho (u - 1) - rho u := by
    dsimp [g] at hadd hu hum ⊢
    linarith
  have hcomp := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 1) g u
  rw [hcomp]
  simpa [g, sub_sub] using hpiece

/-- The normalized unit average in the Dickman equation. -/
lemma rho_ratio_average {u : ℝ} (hu2 : 2 ≤ u) (hu5 : u ≤ 5) :
    (∫ t in (0 : ℝ)..1, rho (u - t) / rho (u - 1)) =
      (u * rho u) / rho (u - 1) := by
  have havg := rho_average_eq (x := u) (by linarith) hu5
  have hcomp := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 1) rho u
  have hshift :
      (∫ t in (0 : ℝ)..1, rho (u - t)) = u * rho u := by
    rw [hcomp]
    simpa using havg.symm
  rw [intervalIntegral.integral_div, hshift]

/-- Exact algebraic form of the first-failure step.  It replaces the
derivative of Tao's nested denominator by a unit-delay integral whose sign
is read directly from earlier values of the logarithmic slope. -/
lemma neg_slopeGrowth_div_sq_eq_integral {u : ℝ}
    (hu2 : 2 < u) (hu5 : u ≤ 5) :
    -slopeGrowth u / dickmanLogSlope u ^ 2 =
      ∫ t in (0 : ℝ)..1,
        (rho (u - t) / rho (u - 1)) *
          (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t)) := by
  have hru : 0 < rho u := rho_pos_on_zero_five (by linarith) hu5
  have hrum1 : 0 < rho (u - 1) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hrum2 : 0 < rho (u - 2) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hum10 : u - 1 ≠ 0 := ne_of_gt (by linarith)
  let R : ℝ → ℝ := fun t => rho (u - t) / rho (u - 1)
  let D : ℝ → ℝ := fun t => rho (u - t - 1) / (u - t) / rho (u - 1)
  have hRcont : Continuous R := by
    dsimp [R]
    exact (continuous_rho.comp
      (continuous_const.sub continuous_id)).div_const _
  have hDcont : ContinuousOn D (Icc (0 : ℝ) 1) := by
    dsimp [D]
    apply ContinuousOn.div_const
    apply ContinuousOn.div
    · exact (continuous_rho.comp
        ((continuous_const.sub continuous_id).sub continuous_const)).continuousOn
    · exact (continuous_const.sub continuous_id).continuousOn
    · intro t ht
      exact ne_of_gt (by linarith [ht.2, hu2])
  have hRint : IntervalIntegrable R volume (0 : ℝ) 1 :=
    hRcont.intervalIntegrable 0 1
  have hDint : IntervalIntegrable D volume (0 : ℝ) 1 := by
    rw [← uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hDcont
    exact hDcont.intervalIntegrable
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      R t * (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t)) =
        dickmanLogSlope (u - 1) * R t - D t := by
    have hut0 : u - t ≠ 0 := ne_of_gt (by linarith [ht.2, hu2])
    have hrut : 0 < rho (u - t) :=
      rho_pos_on_zero_five (by linarith [ht.2, hu2]) (by linarith [ht.1, hu5])
    dsimp [R, D]
    unfold dickmanLogSlope
    field_simp [hu0, hum10, hut0, ne_of_gt hru, ne_of_gt hrum1,
      ne_of_gt hrum2, ne_of_gt hrut]
  rw [show (∫ t in (0 : ℝ)..1,
      R t * (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t))) =
        ∫ t in (0 : ℝ)..1, dickmanLogSlope (u - 1) * R t - D t by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint t (by
        simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)]
  rw [intervalIntegral.integral_sub
    (hRint.const_mul (dickmanLogSlope (u - 1))) hDint]
  rw [intervalIntegral.integral_const_mul]
  change -slopeGrowth u / dickmanLogSlope u ^ 2 =
    dickmanLogSlope (u - 1) *
        (∫ t in (0 : ℝ)..1, rho (u - t) / rho (u - 1)) -
      ∫ t in (0 : ℝ)..1, rho (u - t - 1) / (u - t) / rho (u - 1)
  rw [rho_ratio_average hu2.le hu5]
  rw [intervalIntegral.integral_div,
    rho_delay_unitIntegral hu2.le hu5]
  unfold slopeGrowth dickmanLogSlope
  field_simp [hu0, hum10, ne_of_gt hru, ne_of_gt hrum1, ne_of_gt hrum2]
  ring



lemma continuousOn_dickmanLogSlope_open :
    ContinuousOn dickmanLogSlope (Ioo (1 : ℝ) 5) := by
  unfold dickmanLogSlope
  apply ContinuousOn.div
  · exact (continuous_rho.comp
      (continuous_id.sub continuous_const)).continuousOn
  · exact (continuous_id.mul continuous_rho).continuousOn
  · intro x hx
    exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
      (ne_of_gt (rho_pos_on_zero_five (by linarith [hx.1]) hx.2.le))

lemma continuousOn_dickmanLogSlope_one_to_nine_halves :
    ContinuousOn dickmanLogSlope (Icc (1 : ℝ) (9 / 2 : ℝ)) := by
  unfold dickmanLogSlope
  apply ContinuousOn.div
  · exact (continuous_rho.comp
      (continuous_id.sub continuous_const)).continuousOn
  · exact (continuous_id.mul continuous_rho).continuousOn
  · intro x hx
    exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
      (ne_of_gt (rho_pos_on_zero_five (by linarith [hx.1])
        (by norm_num at hx ⊢; linarith [hx.2])))

/-- On the first nonconstant Dickman interval the numerator of the slope is
still `1`, so the derivative has this simpler exact form. -/
lemma hasDerivAt_dickmanLogSlope_one_two {u : ℝ}
    (hu1 : 1 < u) (hu2 : u < 2) :
    HasDerivAt dickmanLogSlope
      (dickmanLogSlope u * (dickmanLogSlope u - 1 / u)) u := by
  have heq : (fun z : ℝ => rho (z - 1)) =ᶠ[nhds u] (fun _ => (1 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hu2] with z hz
    have hz' : z < 2 := by simpa only [mem_Iio] using hz
    exact rho_eq_one_of_le_one (by linarith [hz'])
  have hnum : HasDerivAt (fun z : ℝ => rho (z - 1)) 0 u := by
    simpa using (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq heq
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hden : HasDerivAt (fun z : ℝ => z * rho z)
      (rho u + u * (-rho (u - 1) / u)) u := by
    simpa [id] using (hasDerivAt_id u).mul
      (hasDerivAt_rho hu1 (by linarith))
  have hru : 0 < rho u := rho_pos_on_zero_five (by linarith) (by linarith)
  have hrum1 : rho (u - 1) = 1 := rho_eq_one_of_le_one (by linarith)
  have hden0 : u * rho u ≠ 0 := mul_ne_zero hu0 (ne_of_gt hru)
  have hraw := hnum.div hden hden0
  apply hraw.congr_deriv
  unfold dickmanLogSlope
  rw [hrum1]
  field_simp [hu0, ne_of_gt hru]
  ring

lemma rho_two_eq_one_sub_log_two : rho 2 = 1 - Real.log 2 := by
  have h := rho_integral_eq (x := (2 : ℝ)) (by norm_num) (by norm_num)
  have hint : (∫ t in (1 : ℝ)..2, rho (t - 1) / t) = Real.log 2 := by
    calc
      (∫ t in (1 : ℝ)..2, rho (t - 1) / t) =
          ∫ t in (1 : ℝ)..2, 1 / t := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htmem : t ∈ Icc (1 : ℝ) 2 := by
          simpa [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] using ht
        change rho (t - 1) / t = 1 / t
        rw [rho_eq_one_of_le_one (by linarith [htmem.2])]
      _ = Real.log 2 := by
        rw [integral_one_div_of_pos (by norm_num) (by norm_num)]
        simp
  linarith

/-- The logarithmic slope is already strictly increasing on `[1,2]`. -/
lemma strictMonoOn_dickmanLogSlope_one_two :
    StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (1 : ℝ) 2)
    (continuousOn_dickmanLogSlope_one_to_nine_halves.mono (by
      intro x hx
      exact ⟨hx.1, by norm_num at hx ⊢; linarith [hx.2]⟩))
  intro x hx
  rw [interior_Icc] at hx
  have hderiv := hasDerivAt_dickmanLogSlope_one_two hx.1 hx.2
  rw [hderiv.deriv]
  have hrho : 0 < rho x :=
    rho_pos_on_zero_five (by linarith [hx.1]) (by linarith [hx.2])
  have hrho_lt : rho x < 1 := by
    have hanti := strictAntiOn_rhoGlobal_Ici_one
      (show (1 : ℝ) ∈ Ici 1 by simp)
      (show x ∈ Ici 1 by simpa using hx.1.le) hx.1
    rw [rhoGlobal_eq_one_of_le_one le_rfl,
      rhoGlobal_eq_rho (by linarith [hx.2])] at hanti
    exact hanti
  have hxpos : 0 < x := by linarith [hx.1]
  have hdenpos : 0 < x * rho x := mul_pos hxpos hrho
  have hdenlt : x * rho x < x := by nlinarith
  have hslope_gt : 1 / x < dickmanLogSlope x := by
    unfold dickmanLogSlope
    rw [rho_eq_one_of_le_one (by linarith [hx.2])]
    exact one_div_lt_one_div_of_lt hdenpos hdenlt
  have hslope_pos : 0 < dickmanLogSlope x := by
    unfold dickmanLogSlope
    rw [rho_eq_one_of_le_one (by linarith [hx.2])]
    exact div_pos zero_lt_one (mul_pos hxpos hrho)
  exact mul_pos hslope_pos (sub_pos.mpr hslope_gt)

lemma slopeGrowth_two_pos : 0 < slopeGrowth 2 := by
  have hrho2 : 0 < rho 2 := rho_pos_on_zero_five (by norm_num) (by norm_num)
  have hrho2lt : rho 2 < 1 / 3 := by
    rw [rho_two_eq_one_sub_log_two]
    have hlog := Real.log_two_gt_d9
    norm_num at hlog ⊢
    nlinarith [hlog]
  unfold slopeGrowth dickmanLogSlope
  norm_num [rho_one, rho_zero]
  field_simp [ne_of_gt hrho2]
  nlinarith

/-- Positive recurrence growth after `2` propagates strict monotonicity of
the logarithmic slope from the explicit base interval `[1,2]`. -/
lemma strictMonoOn_dickmanLogSlope_of_growth_pos {x : ℝ}
    (hx2 : 2 ≤ x) (hx9 : x ≤ 9 / 2)
    (hgrowth : ∀ z ∈ Ioo (2 : ℝ) x, 0 < slopeGrowth z) :
    StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) x) := by
  have hupper : StrictMonoOn dickmanLogSlope (Icc (2 : ℝ) x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (2 : ℝ) x)
    · exact continuousOn_dickmanLogSlope_one_to_nine_halves.mono (by
        intro z hz
        exact ⟨by linarith [hz.1], by linarith [hz.2, hx9]⟩)
    · intro z hz
      rw [interior_Icc] at hz
      have hderiv := hasDerivAt_dickmanLogSlope hz.1
        (by norm_num at hx9 ⊢; linarith [hz.2, hx9])
      rw [hderiv.deriv]
      exact hgrowth z hz
  intro a ha b hb hab
  by_cases hb2 : b ≤ 2
  · exact strictMonoOn_dickmanLogSlope_one_two
      ⟨ha.1, hab.le.trans hb2⟩ ⟨by linarith [ha.1], hb2⟩ hab
  by_cases ha2 : 2 ≤ a
  · exact hupper ⟨ha2, ha.2⟩ ⟨by linarith [hb2], hb.2⟩ hab
  · have hleft := strictMonoOn_dickmanLogSlope_one_two
      (show a ∈ Icc (1 : ℝ) 2 from ⟨ha.1, le_of_not_ge ha2⟩)
      (show (2 : ℝ) ∈ Icc (1 : ℝ) 2 by norm_num)
      (lt_of_not_ge ha2)
    have hright := hupper
      (show (2 : ℝ) ∈ Icc 2 x from ⟨le_rfl, hx2⟩)
      (show b ∈ Icc 2 x from ⟨le_of_not_ge hb2, hb.2⟩)
      (lt_of_not_ge hb2)
    exact hleft.trans hright

/-- Strict positivity of the Dickman log-slope growth on the whole range
needed by the covariance kernel.  The proof uses the compact first-failure
principle and the exact algebraic integral identity above. -/
theorem slopeGrowth_pos_on_two_nine_halves :
    ∀ u ∈ Icc (2 : ℝ) (9 / 2 : ℝ), 0 < slopeGrowth u := by
  apply FirstFailure.positiveOn_Icc_of_positive_at_first_failure
    slopeGrowth continuousOn_slopeGrowth_Icc
  intro u hu hprev
  rcases hu.1.eq_or_lt with rfl | hu2
  · exact slopeGrowth_two_pos
  · have hmono : StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) u) :=
      strictMonoOn_dickmanLogSlope_of_growth_pos hu.1 hu.2 (by
        intro z hz
        exact hprev z ⟨hz.1.le, hz.2.le⟩ hz.2)
    let H : ℝ → ℝ := fun t =>
      -((rho (u - t) / rho (u - 1)) *
        (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t)))
    have hRcont : Continuous (fun t : ℝ => rho (u - t) / rho (u - 1)) :=
      (continuous_rho.comp
        (continuous_const.sub continuous_id)).div_const _
    have hfcomp : ContinuousOn (fun t : ℝ => dickmanLogSlope (u - t))
        (Icc (0 : ℝ) 1) := by
      apply continuousOn_dickmanLogSlope_open.comp
        (continuous_const.sub continuous_id).continuousOn
      intro t ht
      change 1 < u - t ∧ u - t < 5
      exact ⟨by linarith [hu2, ht.2], by
        norm_num at hu ⊢
        linarith [hu.2, ht.1]⟩
    have hHcont : ContinuousOn H (Icc (0 : ℝ) 1) := by
      dsimp [H]
      exact (hRcont.continuousOn.mul
        (continuous_const.continuousOn.sub hfcomp)).neg
    have hHnonneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ H t := by
      have hratio : 0 < rho (u - t) / rho (u - 1) :=
        div_pos
          (rho_pos_on_zero_five (by linarith [hu2, ht.2])
            (by norm_num at hu ⊢; linarith [hu.2, ht.1]))
          (rho_pos_on_zero_five (by linarith [hu2])
            (by norm_num at hu ⊢; linarith [hu.2]))
      have hslope : dickmanLogSlope (u - 1) ≤ dickmanLogSlope (u - t) :=
        hmono.monotoneOn
          ⟨by linarith [hu2], by linarith⟩
          ⟨by linarith [hu2, ht.2], by linarith [ht.1]⟩
          (by linarith [ht.2])
      dsimp [H]
      exact neg_nonneg.mpr
        (mul_nonpos_of_nonneg_of_nonpos hratio.le (sub_nonpos.mpr hslope))
    have hHhalf : 0 < H (1 / 2 : ℝ) := by
      have hratio : 0 < rho (u - (1 / 2 : ℝ)) / rho (u - 1) :=
        div_pos
          (rho_pos_on_zero_five (by linarith [hu2])
            (by norm_num at hu ⊢; linarith [hu.2]))
          (rho_pos_on_zero_five (by linarith [hu2])
            (by norm_num at hu ⊢; linarith [hu.2]))
      have hslope : dickmanLogSlope (u - 1) <
          dickmanLogSlope (u - (1 / 2 : ℝ)) :=
        hmono
          ⟨by linarith [hu2], by linarith⟩
          ⟨by linarith [hu2], by linarith⟩
          (by norm_num)
      dsimp [H]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hratio (sub_neg.mpr hslope))
    have hHIntegral : 0 < ∫ t in (0 : ℝ)..1, H t := by
      apply intervalIntegral.integral_pos (show (0 : ℝ) < 1 by norm_num)
        hHcont
      · intro t ht
        exact hHnonneg t ⟨ht.1.le, ht.2⟩
      · exact ⟨(1 / 2 : ℝ), by norm_num, hHhalf⟩
    have hintegralNeg :
        (∫ t in (0 : ℝ)..1,
          (rho (u - t) / rho (u - 1)) *
            (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t))) < 0 := by
      dsimp [H] at hHIntegral
      rw [intervalIntegral.integral_neg] at hHIntegral
      linarith
    have hid := neg_slopeGrowth_div_sq_eq_integral hu2
      (by norm_num at hu ⊢; linarith [hu.2])
    have hquot : -slopeGrowth u / dickmanLogSlope u ^ 2 < 0 := by
      rw [hid]
      exact hintegralNeg
    have hslopePos : 0 < dickmanLogSlope u :=
      dickmanLogSlope_pos hu2.le (by norm_num at hu ⊢; linarith [hu.2])
    have hden : 0 < dickmanLogSlope u ^ 2 := sq_pos_of_pos hslopePos
    have hnum : -slopeGrowth u < 0 := by
      rcases (div_neg_iff.mp hquot) with hbad | hgood
      · exact False.elim ((not_lt_of_ge hden.le) hbad.2)
      · exact hgood.1
    linarith

theorem strictMonoOn_dickmanLogSlope_one_nine_halves :
    StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) (9 / 2 : ℝ)) := by
  apply strictMonoOn_dickmanLogSlope_of_growth_pos (by norm_num) le_rfl
  intro z hz
  exact slopeGrowth_pos_on_two_nine_halves z ⟨hz.1.le, hz.2.le⟩

lemma hasDerivAt_log_rho_eq_neg_slope {x : ℝ} (hx1 : 1 < x) (hx5 : x < 5) :
    HasDerivAt (fun z : ℝ => Real.log (rho z)) (-dickmanLogSlope x) x := by
  have hrho : 0 < rho x :=
    rho_pos_on_zero_five (by linarith) hx5.le
  have hraw := (hasDerivAt_rho hx1 (by linarith)).log (ne_of_gt hrho)
  apply hraw.congr_deriv
  unfold dickmanLogSlope
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  field_simp [hx0, ne_of_gt hrho]

/-- Fundamental-theorem form of the logarithmic derivative, on the entire
range used by the one- and two-point Dickman translates. -/
lemma log_rho_sub_eq_neg_slopeIntegral {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hb : b < 5) :
    Real.log (rho b) - Real.log (rho a) =
      -(∫ x in a..b, dickmanLogSlope x) := by
  have hcontLog : ContinuousOn (fun x : ℝ => Real.log (rho x)) (Icc a b) := by
    apply ContinuousOn.log continuous_rho.continuousOn
    intro x hx
    exact ne_of_gt (rho_pos_on_zero_five
      (by linarith [ha, hx.1]) (by linarith [hb, hx.2]))
  have hcontSlope : ContinuousOn (fun x : ℝ => -dickmanLogSlope x)
      (Icc a b) :=
    (continuousOn_dickmanLogSlope_open.mono (by
      intro x hx
      exact ⟨by linarith [ha, hx.1], by linarith [hb, hx.2]⟩)).neg
  have hFTC :
      (∫ x in a..b, -dickmanLogSlope x) =
        Real.log (rho b) - Real.log (rho a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcontLog
    · intro x hx
      exact hasDerivAt_log_rho_eq_neg_slope
        (by linarith [ha, hx.1]) (by linarith [hb, hx.2])
    · exact hcontSlope.intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_neg] at hFTC
  linarith



















































































/-! ## Unconditional covariance consequences -/















end Erdos390.Full.PoissonDickmanDirichlet

end

/- Source module: Erdos390.Full.PoissonDickmanWeightedInverse -/
section


/-!
# A deterministic weighted `L∞` quotient inverse

After writing the Poisson--Dickman test as `f(t)=t q(t)`, the covariance
operator is a nonlocal graph Laplacian with continuous edge kernel
`-K(s,t)/s`.  Strict Dickman log-concavity makes this edge kernel uniformly
positive when the second endpoint ranges in one fixed interior interval,
including at the removable axis `s=0`.  A maximum/minimum argument then
controls the oscillation of `q` directly.  This gives the weighted quotient
inverse without assuming Fredholm theory or an inverse theorem.
-/

open Set

noncomputable section

set_option maxHeartbeats 800000

namespace Erdos390.Full.PoissonDickmanWeightedInverse

open MeasureTheory
open DickmanBasic ConditionedPoissonLimit PoissonDickmanDirichlet

lemma FdifferenceQuotient_zero_right {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) :
    FdifferenceQuotient a 0 = deriv F a := by
  unfold FdifferenceQuotient
  have ha2 : a ∈ Icc (0 : ℝ) 2 := ⟨ha.1, ha.2.trans (by norm_num)⟩
  simp only [mul_zero, add_zero]
  rw [derivFExtension_eq_deriv_of_mem ha2]
  simp

/-- The derivative of the normalized Dickman translate is its value times
the Dickman logarithmic slope. -/
lemma deriv_F_eq_mul_dickmanLogSlope {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv F x = F x * dickmanLogSlope (U - x) := by
  have hu1 : 1 < U - x := by norm_num [U] at hx ⊢; linarith [hx.2]
  have hu6 : U - x ≤ 6 := by norm_num [U] at hx ⊢; linarith [hx.1]
  have hinner : HasDerivAt (fun z : ℝ => U - z) (-1) x := by
    simpa using (hasDerivAt_const x U).sub (hasDerivAt_id x)
  have hcomp := (hasDerivAt_rho hu1 hu6).comp x hinner
  have hdiv := hcomp.div_const (rho U)
  have hU : rho U ≠ 0 := ne_of_gt rho_U_pos
  have hFderiv : HasDerivAt F
      (-rho (U - x - 1) / (U - x) * -1 / rho U) x := by
    simpa [F, Function.comp_def] using hdiv
  rw [hFderiv.deriv]
  unfold F dickmanLogSlope
  have hUx0 : 0 < U - x := by linarith
  have hUx5 : U - x < 5 := by
    norm_num [U] at hx ⊢
    linarith [hx.1]
  have hRho : rho (U - x) ≠ 0 :=
    ne_of_gt (rho_pos_on_zero_five hUx0.le hUx5.le)
  field_simp [hU, ne_of_gt hUx0, hRho]

lemma covarianceKernelQuotient_axis_formula {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernelQuotient t 0 =
      F t * (dickmanLogSlope (U - t) - dickmanLogSlope U) := by
  unfold covarianceKernelQuotient
  rw [FdifferenceQuotient_zero_right ht,
    FdifferenceQuotient_zero_right (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num),
    deriv_F_eq_mul_dickmanLogSlope ht,
    deriv_F_eq_mul_dickmanLogSlope
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)]
  simp only [F_zero, one_mul]
  ring

/-- Strict negativity survives at the removable `s=0` axis. -/
theorem covarianceKernelQuotient_axis_neg {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    covarianceKernelQuotient t 0 < 0 := by
  have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  rw [covarianceKernelQuotient_axis_formula htcc]
  have hUt : U - t ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    norm_num [U] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hU : U ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by norm_num [U]
  have hslope : dickmanLogSlope (U - t) < dickmanLogSlope U :=
    strictMonoOn_dickmanLogSlope_one_nine_halves hUt hU (by linarith [ht.1])
  exact mul_neg_of_pos_of_neg
    (F_pos ⟨htcc.1, htcc.2.trans (by norm_num)⟩)
    (sub_neg.mpr hslope)

/-! The strict four-point inequality with one endpoint allowed to equal one.
The proof repeats the already audited shifted-slope integral argument, but
uses only positivity (not strict upper bounds) for the endpoints. -/

 lemma slopeIntegral_shift_lt_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x in (U - s - t)..(U - s), dickmanLogSlope x) <
      ∫ x in (U - t)..U, dickmanLogSlope x := by
  have hab : U - s - t < U - s := by linarith [ht.1]
  have hxmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.1, hx.2]
  have hxsmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x + s ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [ht.2, hx.1]
    · norm_num [U] at hs hx ⊢
      linarith [hs.2, hx.2]
  have hcont₁ : ContinuousOn dickmanLogSlope (Icc (U - s - t) (U - s)) :=
    continuousOn_dickmanLogSlope_one_to_nine_halves.mono hxmem
  have hcont₂ : ContinuousOn (fun x : ℝ => dickmanLogSlope (x + s))
      (Icc (U - s - t) (U - s)) := by
    apply continuousOn_dickmanLogSlope_one_to_nine_halves.comp
      (continuous_id.add continuous_const).continuousOn
    exact hxsmem
  have hle : ∀ x ∈ Ioc (U - s - t) (U - s),
      dickmanLogSlope x ≤ dickmanLogSlope (x + s) := by
    intro x hx
    apply strictMonoOn_dickmanLogSlope_one_nine_halves.monotoneOn
    · exact hxmem x ⟨hx.1.le, hx.2⟩
    · exact hxsmem x ⟨hx.1.le, hx.2⟩
    · linarith [hs.1]
  have hexists : ∃ c ∈ Icc (U - s - t) (U - s),
      dickmanLogSlope c < dickmanLogSlope (c + s) := by
    refine ⟨U - s - t, left_mem_Icc.mpr hab.le, ?_⟩
    apply strictMonoOn_dickmanLogSlope_one_nine_halves
    · exact hxmem _ (left_mem_Icc.mpr hab.le)
    · exact hxsmem _ (left_mem_Icc.mpr hab.le)
    · linarith [hs.1]
  have hint := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab hcont₁ hcont₂ hle hexists
  rw [intervalIntegral.integral_comp_add_right] at hint
  convert hint using 1
  all_goals ring

lemma log_rho_four_point_lt_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Real.log (rho (U - s - t)) + Real.log (rho U) <
      Real.log (rho (U - s)) + Real.log (rho (U - t)) := by
  have h₁ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - s - t) (b := U - s)
    (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
    (by linarith [ht.1])
    (by norm_num [U] at hs ⊢; linarith [hs.1])
  have h₂ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - t) (b := U)
    (by norm_num [U] at ht ⊢; linarith [ht.2])
    (by linarith [ht.1]) (by norm_num [U])
  have hint := slopeIntegral_shift_lt_closed hs ht
  linarith

lemma rho_four_point_lt_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    rho (U - s - t) * rho U < rho (U - s) * rho (U - t) := by
  have ha : 0 < rho (U - s - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
      (by norm_num [U] at hs ht ⊢; linarith [hs.1, ht.1])
  have hb : 0 < rho U := rho_U_pos
  have hc : 0 < rho (U - s) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ⊢; linarith [hs.2])
      (by norm_num [U] at hs ⊢; linarith [hs.1])
  have hd : 0 < rho (U - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at ht ⊢; linarith [ht.2])
      (by norm_num [U] at ht ⊢; linarith [ht.1])
  have h := Real.exp_lt_exp.mpr (log_rho_four_point_lt_closed hs ht)
  rw [Real.exp_add, Real.exp_add, Real.exp_log ha, Real.exp_log hb,
    Real.exp_log hc, Real.exp_log hd] at h
  exact h

theorem covarianceKernel_neg_closed {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    covarianceKernel s t < 0 := by
  have hprod := rho_four_point_lt_closed hs ht
  have hU : 0 < rho U := rho_U_pos
  have hden : 0 < rho U * rho U := mul_pos hU hU
  have hscaled := (div_lt_div_iff_of_pos_right hden).2 hprod
  unfold covarianceKernel F
  apply sub_neg.mpr
  calc
    rho (U - (s + t)) / rho U =
        (rho (U - s - t) * rho U) / (rho U * rho U) := by
      rw [show U - (s + t) = U - s - t by ring]
      field_simp [ne_of_gt hU]
    _ < (rho (U - s) * rho (U - t)) / (rho U * rho U) := hscaled
    _ = rho (U - s) / rho U * (rho (U - t) / rho U) := by
      field_simp [ne_of_gt hU]

/-- The transposed removable quotient is strictly negative for every first
coordinate, including both boundary points, once the second coordinate is
interior. -/
theorem covarianceKernelQuotient_transpose_neg {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    covarianceKernelQuotient t s < 0 := by
  by_cases hs0 : s = 0
  · subst s
    exact covarianceKernelQuotient_axis_neg ht
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hkernel : covarianceKernel t s < 0 :=
      covarianceKernel_neg_closed
        ⟨ht.1, ht.2.le⟩ ⟨hspos, hs.2⟩
    have hmul := mul_covarianceKernelQuotient_eq_kernel
      (s := t) (t := s) ⟨ht.1.le, ht.2.le⟩ hs
    nlinarith

/-- Compactness upgrades strict negativity to one uniform edge-weight lower
bound.  The first coordinate includes the moving-low axis. -/
theorem exists_transposeQuotient_uniform_gap {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s := by
  let S : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) 1 ×ˢ Icc epsilon (1 - epsilon)
  have hnonempty : S.Nonempty := by
    exact ⟨(0, epsilon), by constructor <;> constructor <;> linarith⟩
  have hcompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun z : ℝ × ℝ => -covarianceKernelQuotient z.2 z.1) S :=
    (continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)).neg.continuousOn
  obtain ⟨z, hzS, hzmin⟩ := hcompact.exists_isMinOn hnonempty hcont
  let kappa := -covarianceKernelQuotient z.2 z.1
  have hzt : z.2 ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨hepsilon.trans_le hzS.2.1, by linarith [hzS.2.2, hepsilon]⟩
  have hkappa : 0 < kappa := by
    dsimp only [kappa]
    exact neg_pos.mpr (covarianceKernelQuotient_transpose_neg hzS.1 hzt)
  refine ⟨kappa, hkappa, ?_⟩
  intro s hs t ht
  change -covarianceKernelQuotient z.2 z.1 ≤
    -covarianceKernelQuotient t s
  exact hzmin (show (s, t) ∈ S by exact ⟨hs, ht⟩)

/-! ## The weighted operator as a graph Laplacian -/



















end Erdos390.Full.PoissonDickmanWeightedInverse

end

/- Source module: Erdos390.Full.FiniteGraphQuotientInverse -/
section


/-!
# Mesh-independent inverse for a finite nonlocal graph Laplacian

This is the finite compression of the maximum/minimum argument used by the
weighted Poisson--Dickman quotient inverse.  A common positive anchor measure
seen by every row gives an oscillation bound independent of the number or
shape of cells.  Projection to any positive weighted gauge then gives an
actual inverse bound on that gauge; no inverse is an input.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band] [DecidableEq Band]

def graphOperator (edge : Band → Band → ℝ) (q : Band → ℝ) (i : Band) : ℝ :=
  ∑ j, edge i j * (q i - q j)

def weightTotal (omega : Band → ℝ) : ℝ :=
  ∑ i, omega i

def weightedMean (omega x : Band → ℝ) : ℝ :=
  (∑ i, omega i * x i) / weightTotal omega

def meanProjection (omega x : Band → ℝ) (i : Band) : ℝ :=
  x i - weightedMean omega x



omit [DecidableEq Band] in
lemma graphOperator_at_max_nonneg
    (edge : Band → Band → ℝ) (q : Band → ℝ) {imax : Band}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hmax : ∀ j, q imax ≥ q j) :
    0 ≤ graphOperator edge q imax := by
  unfold graphOperator
  exact Finset.sum_nonneg fun j hj =>
    mul_nonneg (hedge imax j) (sub_nonneg.mpr (hmax j))

omit [DecidableEq Band] in
lemma graphOperator_at_min_nonpos
    (edge : Band → Band → ℝ) (q : Band → ℝ) {imin : Band}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hmin : ∀ j, q imin ≤ q j) :
    graphOperator edge q imin ≤ 0 := by
  unfold graphOperator
  exact Finset.sum_nonpos fun j hj =>
    mul_nonpos_of_nonneg_of_nonpos (hedge imin j)
      (sub_nonpos.mpr (hmin j))

omit [DecidableEq Band] in
/-- Uniform edge domination by one anchor measure controls oscillation. -/
theorem exists_center_of_graphOperator_bound
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor q : Band → ℝ)
    {kappa G : ℝ}
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (hbound : ∀ i, |graphOperator edge q i| ≤ G) :
    ∃ mu : ℝ, ∀ i,
      |q i - mu| ≤ G / (kappa * ∑ j, anchor j) := by
  obtain ⟨imax, himax, hmax'⟩ :=
    Finset.exists_max_image Finset.univ q Finset.univ_nonempty
  obtain ⟨imin, himin, hmin'⟩ :=
    Finset.exists_min_image Finset.univ q Finset.univ_nonempty
  have hmax (j : Band) : q j ≤ q imax := by
    exact hmax' j (Finset.mem_univ j)
  have hmin (j : Band) : q imin ≤ q j := by
    exact hmin' j (Finset.mem_univ j)
  have hmaxLower :
      kappa * ∑ j, anchor j * (q imax - q j) ≤
        graphOperator edge q imax := by
    unfold graphOperator
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hdiff : 0 ≤ q imax - q j := sub_nonneg.mpr (hmax j)
    calc
      kappa * (anchor j * (q imax - q j)) =
          (kappa * anchor j) * (q imax - q j) := by ring
      _ ≤ edge imax j * (q imax - q j) :=
        mul_le_mul_of_nonneg_right (hdom imax j) hdiff
  have hminLower :
      kappa * ∑ j, anchor j * (q j - q imin) ≤
        -graphOperator edge q imin := by
    unfold graphOperator
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have hdiff : 0 ≤ q j - q imin := sub_nonneg.mpr (hmin j)
    calc
      kappa * (anchor j * (q j - q imin)) =
          (kappa * anchor j) * (q j - q imin) := by ring
      _ ≤ edge imin j * (q j - q imin) :=
        mul_le_mul_of_nonneg_right (hdom imin j) hdiff
      _ = -(edge imin j * (q imin - q j)) := by ring
  have hoperatorUpper :
      graphOperator edge q imax + (-graphOperator edge q imin) ≤ 2 * G := by
    have hmaxBound := hbound imax
    have hminBound := hbound imin
    have h₁ : graphOperator edge q imax ≤ G :=
      (le_abs_self _).trans hmaxBound
    have h₂ : -graphOperator edge q imin ≤ G :=
      (neg_le_abs _).trans hminBound
    linarith
  have hsumIdentity :
      (∑ j, anchor j * (q imax - q j)) +
          (∑ j, anchor j * (q j - q imin)) =
        (∑ j, anchor j) * (q imax - q imin) := by
    rw [← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hoscScaled :
      (kappa * ∑ j, anchor j) * (q imax - q imin) ≤ 2 * G := by
    calc
      (kappa * ∑ j, anchor j) * (q imax - q imin) =
          kappa * ((∑ j, anchor j * (q imax - q j)) +
            ∑ j, anchor j * (q j - q imin)) := by
        rw [hsumIdentity]
        ring
      _ = kappa * (∑ j, anchor j * (q imax - q j)) +
          kappa * (∑ j, anchor j * (q j - q imin)) := by ring
      _ ≤ graphOperator edge q imax + (-graphOperator edge q imin) :=
        add_le_add hmaxLower hminLower
      _ ≤ 2 * G := hoperatorUpper
  have hden : 0 < kappa * ∑ j, anchor j :=
    mul_pos hkappa hanchorTotal
  have hosc : q imax - q imin ≤
      2 * G / (kappa * ∑ j, anchor j) := by
    exact (le_div_iff₀ hden).2 (by
      simpa only [mul_comm] using hoscScaled)
  refine ⟨(q imax + q imin) / 2, ?_⟩
  intro i
  rw [abs_le]
  constructor
  · have hhalf : (q imax - q imin) / 2 ≤
        G / (kappa * ∑ j, anchor j) := by
      calc
        (q imax - q imin) / 2 ≤
            (2 * G / (kappa * ∑ j, anchor j)) / 2 := by linarith
        _ = G / (kappa * ∑ j, anchor j) := by ring
    linarith [hmin i]
  · have hhalf : (q imax - q imin) / 2 ≤
        G / (kappa * ∑ j, anchor j) := by
      calc
        (q imax - q imin) / 2 ≤
            (2 * G / (kappa * ∑ j, anchor j)) / 2 := by linarith
        _ = G / (kappa * ∑ j, anchor j) := by ring
    linarith [hmax i]

omit [DecidableEq Band] in
/-- Projecting the graph operator to an arbitrary positive weighted gauge
still has a uniform inverse bound.  This is a conclusion from the edge
geometry, not an inverse hypothesis. -/
theorem abs_le_of_gauge_projectedGraph_bound
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega q : Band → ℝ)
    {kappa G : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (hgauge : ∑ i, omega i * q i = 0)
    (hprojected : ∀ i,
      |meanProjection omega (graphOperator edge q) i| ≤ G) :
    ∀ i, |q i| ≤ 4 * G / (kappa * ∑ j, anchor j) := by
  let c := weightedMean omega (graphOperator edge q)
  obtain ⟨imax, himax, hmax'⟩ :=
    Finset.exists_max_image Finset.univ q Finset.univ_nonempty
  obtain ⟨imin, himin, hmin'⟩ :=
    Finset.exists_min_image Finset.univ q Finset.univ_nonempty
  have hmax (j : Band) : q j ≤ q imax :=
    hmax' j (Finset.mem_univ j)
  have hmin (j : Band) : q imin ≤ q j :=
    hmin' j (Finset.mem_univ j)
  have hgraphMax : 0 ≤ graphOperator edge q imax :=
    graphOperator_at_max_nonneg edge q hedge (fun j => hmax j)
  have hgraphMin : graphOperator edge q imin ≤ 0 :=
    graphOperator_at_min_nonpos edge q hedge (fun j => hmin j)
  have hprojMax := hprojected imax
  have hprojMin := hprojected imin
  have hcLower : -G ≤ c := by
    unfold meanProjection at hprojMax
    dsimp only [c]
    have := le_of_abs_le hprojMax
    linarith [hgraphMax]
  have hcUpper : c ≤ G := by
    unfold meanProjection at hprojMin
    dsimp only [c]
    have := neg_le_of_abs_le hprojMin
    linarith [hgraphMin]
  have hgraphBound (i : Band) : |graphOperator edge q i| ≤ 2 * G := by
    have hi := hprojected i
    unfold meanProjection at hi
    dsimp only [c] at hcLower hcUpper ⊢
    rw [abs_le] at hi ⊢
    constructor <;> linarith [hi.1, hi.2]
  obtain ⟨mu, hmu⟩ := exists_center_of_graphOperator_bound
    edge anchor q hdom hkappa hanchorTotal hgraphBound
  have hmuAbs : |mu| ≤ 2 * G / (kappa * ∑ j, anchor j) := by
    have htotal0 : (∑ i, omega i) ≠ 0 := ne_of_gt homegaTotal
    have hidentity :
        mu = (∑ i, omega i * (mu - q i)) /
          (∑ i, omega i) := by
      have hsum :
          (∑ i, omega i * (mu - q i)) = mu * (∑ i, omega i) := by
        calc
          (∑ i, omega i * (mu - q i)) =
              (∑ i, omega i * mu) - ∑ i, omega i * q i := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = mu * (∑ i, omega i) := by
            rw [hgauge, sub_zero]
            calc
              (∑ i, omega i * mu) = (∑ i, omega i) * mu :=
                (Finset.sum_mul Finset.univ omega mu).symm
              _ = mu * (∑ i, omega i) := by ring
      rw [hsum]
      apply (eq_div_iff htotal0).2
      ring
    rw [hidentity, abs_div, abs_of_pos homegaTotal]
    calc
      |∑ i, omega i * (mu - q i)| / (∑ i, omega i) ≤
          (∑ i, omega i *
            (2 * G / (kappa * ∑ j, anchor j))) /
              (∑ i, omega i) := by
        apply div_le_div_of_nonneg_right _ homegaTotal.le
        calc
          |∑ i, omega i * (mu - q i)| ≤
              ∑ i, |omega i * (mu - q i)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, omega i *
              (2 * G / (kappa * ∑ j, anchor j)) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [abs_mul, abs_of_nonneg (homega i), abs_sub_comm]
            exact mul_le_mul_of_nonneg_left (hmu i) (homega i)
      _ = 2 * G / (kappa * ∑ j, anchor j) := by
        rw [← Finset.sum_mul]
        field_simp [htotal0]
  intro i
  calc
    |q i| = |(q i - mu) + mu| := by ring_nf
    _ ≤ |q i - mu| + |mu| := abs_add_le _ _
    _ ≤ 2 * G / (kappa * ∑ j, anchor j) +
        2 * G / (kappa * ∑ j, anchor j) :=
      add_le_add (hmu i) hmuAbs
    _ = 4 * G / (kappa * ∑ j, anchor j) := by ring

end Erdos390.Full.FiniteGraphQuotientInverse

end

/- Source module: Erdos390.Full.FiniteGraphStableInverse -/
section


/-!
# Stable inversion on the actual finite gauge

The graph edge geometry proved at the continuum level is turned here into a
linear equivalence on the *actual* weighted gauge.  Its inverse and inverse
bound are conclusions of the maximum/minimum theorem.  A sufficiently small
operator error is then transferred by `StableInverse`; the perturbed inverse
is never assumed.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteGraphStableInverse

open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]

def gaugeFunctional (omega : Band → ℝ) :
    (Band → ℝ) →ₗ[ℝ] ℝ where
  toFun q := ∑ i, omega i * q i
  map_add' q r := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  map_smul' c q := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      (∑ i, omega i * (c * q i)) =
          ∑ i, c * (omega i * q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, (omega i * q i) * c := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, omega i * q i) * c :=
        (Finset.sum_mul Finset.univ (fun i => omega i * q i) c).symm
      _ = c * ∑ i, omega i * q i := by ring

def gaugeSubmodule (omega : Band → ℝ) : Submodule ℝ (Band → ℝ) :=
  LinearMap.ker (gaugeFunctional omega)

abbrev GaugeSpace (omega : Band → ℝ) := gaugeSubmodule omega



lemma weighted_sum_meanProjection
    (omega x : Band → ℝ)
    (hTotal : (∑ i, omega i) ≠ 0) :
    ∑ i, omega i * meanProjection omega x i = 0 := by
  unfold meanProjection weightedMean weightTotal
  calc
    (∑ i, omega i *
        (x i - (∑ j, omega j * x j) / ∑ j, omega j)) =
        (∑ i, omega i * x i) -
          (∑ i, omega i) *
            ((∑ j, omega j * x j) / ∑ j, omega j) := by
      calc
        (∑ i, omega i *
            (x i - (∑ j, omega j * x j) / ∑ j, omega j)) =
            (∑ i, omega i * x i) -
              ∑ i, omega i *
                ((∑ j, omega j * x j) / ∑ j, omega j) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          rw [← Finset.sum_mul]
    _ = 0 := by
      field_simp [hTotal]
      ring

lemma graphOperator_add (edge : Band → Band → ℝ)
    (q r : Band → ℝ) (i : Band) :
    graphOperator edge (q + r) i =
      graphOperator edge q i + graphOperator edge r i := by
  unfold graphOperator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.add_apply]
  ring

lemma graphOperator_smul (edge : Band → Band → ℝ)
    (c : ℝ) (q : Band → ℝ) (i : Band) :
    graphOperator edge (c • q) i = c * graphOperator edge q i := by
  unfold graphOperator
  calc
    (∑ j, edge i j * ((c • q) i - (c • q) j)) =
        ∑ j, c * (edge i j * (q i - q j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = ∑ j, (edge i j * (q i - q j)) * c := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j, edge i j * (q i - q j)) * c :=
      (Finset.sum_mul Finset.univ
        (fun j => edge i j * (q i - q j)) c).symm
    _ = c * ∑ j, edge i j * (q i - q j) := by ring

lemma weightedMean_add (omega x y : Band → ℝ) :
    weightedMean omega (x + y) =
      weightedMean omega x + weightedMean omega y := by
  unfold weightedMean weightTotal
  have hsum :
      (∑ i, omega i * (x + y) i) =
        (∑ i, omega i * x i) + ∑ i, omega i * y i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.add_apply]
    ring
  rw [hsum]
  ring

lemma weightedMean_smul (omega : Band → ℝ) (c : ℝ) (x : Band → ℝ) :
    weightedMean omega (c • x) = c * weightedMean omega x := by
  unfold weightedMean weightTotal
  have hsum :
      (∑ i, omega i * (c • x) i) =
        c * ∑ i, omega i * x i := by
    calc
      (∑ i, omega i * (c • x) i) =
          ∑ i, c * (omega i * x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = ∑ i, (omega i * x i) * c := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, omega i * x i) * c :=
        (Finset.sum_mul Finset.univ (fun i => omega i * x i) c).symm
      _ = c * ∑ i, omega i * x i := by ring
  rw [hsum]
  ring

lemma meanProjection_add (omega x y : Band → ℝ) (i : Band) :
    meanProjection omega (x + y) i =
      meanProjection omega x i + meanProjection omega y i := by
  unfold meanProjection
  rw [weightedMean_add]
  simp only [Pi.add_apply]
  ring

lemma meanProjection_smul (omega : Band → ℝ) (c : ℝ)
    (x : Band → ℝ) (i : Band) :
    meanProjection omega (c • x) i =
      c * meanProjection omega x i := by
  unfold meanProjection
  rw [weightedMean_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

def projectedGraphLinearMap
    (edge : Band → Band → ℝ) (omega : Band → ℝ)
    (hTotal : (∑ i, omega i) ≠ 0) :
    GaugeSpace omega →ₗ[ℝ] GaugeSpace omega where
  toFun q :=
    ⟨meanProjection omega (graphOperator edge q.1),
      weighted_sum_meanProjection omega (graphOperator edge q.1) hTotal⟩
  map_add' q r := by
    apply Subtype.ext
    funext i
    change meanProjection omega
        (graphOperator edge ((q : Band → ℝ) + (r : Band → ℝ))) i =
      meanProjection omega (graphOperator edge (q : Band → ℝ)) i +
        meanProjection omega (graphOperator edge (r : Band → ℝ)) i
    rw [show graphOperator edge
        ((q : Band → ℝ) + (r : Band → ℝ)) =
        graphOperator edge (q : Band → ℝ) +
          graphOperator edge (r : Band → ℝ) by
      funext j
      exact graphOperator_add edge (q : Band → ℝ) (r : Band → ℝ) j]
    exact meanProjection_add omega _ _ i
  map_smul' c q := by
    apply Subtype.ext
    funext i
    change meanProjection omega
        (graphOperator edge (c • (q : Band → ℝ))) i =
      c * meanProjection omega (graphOperator edge (q : Band → ℝ)) i
    rw [show graphOperator edge (c • (q : Band → ℝ)) =
        c • graphOperator edge (q : Band → ℝ) by
      funext j
      exact graphOperator_smul edge c (q : Band → ℝ) j]
    exact meanProjection_smul omega c _ i

/-- Edge domination proves injectivity on the actual weighted gauge. -/
theorem projectedGraphLinearMap_injective
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i) :
    Function.Injective
      (projectedGraphLinearMap edge omega (ne_of_gt homegaTotal)) := by
  intro q r hqr
  have hzero : projectedGraphLinearMap edge omega (ne_of_gt homegaTotal)
      (q - r) = 0 := by
    rw [map_sub, hqr, sub_self]
  have hgauge : ∑ i, omega i * ((q - r : GaugeSpace omega).1 i) = 0 :=
    (q - r : GaugeSpace omega).2
  have hprojected (i : Band) :
      |meanProjection omega
        (graphOperator edge (q - r : GaugeSpace omega).1) i| ≤ 0 := by
    have happ := congrArg
      (fun x : GaugeSpace omega => (x : Band → ℝ) i) hzero
    have habs :
        |meanProjection omega
          (graphOperator edge (q - r : GaugeSpace omega).1) i| = 0 := by
      simpa only [projectedGraphLinearMap, Submodule.coe_zero,
        Pi.zero_apply, abs_zero] using congrArg abs happ
    exact habs.le
  have hbound := abs_le_of_gauge_projectedGraph_bound
    edge anchor omega (q - r : GaugeSpace omega).1
    (kappa := kappa) (G := 0) hedge hdom hkappa hanchorTotal
    homega homegaTotal hgauge hprojected
  have hfun : (q - r : GaugeSpace omega).1 = 0 := by
    funext i
    have hi := hbound i
    simp only [zero_div, mul_zero, abs_nonpos_iff] at hi
    exact hi
  apply sub_eq_zero.mp
  exact Subtype.ext hfun

/-- The reference graph equivalence.  It is constructed from injectivity in
finite dimension, not stored as mesh data. -/
def referenceGraphEquiv
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i) :
    GaugeSpace omega ≃L[ℝ] GaugeSpace omega :=
  (LinearEquiv.ofInjectiveEndo
    (projectedGraphLinearMap edge omega (ne_of_gt homegaTotal))
    (projectedGraphLinearMap_injective edge anchor omega hedge hdom
      hkappa hanchorTotal homega homegaTotal)).toContinuousLinearEquiv

def referenceGraphCLM
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i) :
    GaugeSpace omega →L[ℝ] GaugeSpace omega :=
  (referenceGraphEquiv edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal).toContinuousLinearMap

def referenceGraphInvCLM
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i) :
    GaugeSpace omega →L[ℝ] GaugeSpace omega :=
  (referenceGraphEquiv edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal).symm.toContinuousLinearMap







end Erdos390.Full.FiniteGraphStableInverse

end

/- Source module: Erdos390.Full.ContinuumCellGraph -/
section


/-!
# Continuum cell compression as a finite graph

This is the mesh-uniform bridge from the weighted Poisson--Dickman operator
to a finite matrix.  Every row is the ordinary-cell average of the graph
kernel `-K(t,s)/s`.  A fixed collection of cells lying in one interior
interval supplies a common anchor measure.  The positive edge constant is
derived from the Dickman kernel theorem; it is not mesh data.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph

open MeasureTheory
open ConditionedPoissonLimit
open PoissonDickmanWeightedInverse

variable {Band : Type*} [Fintype Band] [DecidableEq Band]

/-- Elementary interval geometry for a finite mesh.  `interiorCells` only
records which cells lie in the fixed compact interval; its positive total
length is a geometric coverage statement, not an operator gap. -/
structure IntervalMesh (epsilon : ℝ) (Band : Type*) [Fintype Band] where
  lower : Band → ℝ
  upper : Band → ℝ
  lower_pos : ∀ i, 0 < lower i
  lower_lt_upper : ∀ i, lower i < upper i
  upper_le_one : ∀ i, upper i ≤ 1
  interiorCells : Finset Band
  interior_lower : ∀ i ∈ interiorCells, epsilon ≤ lower i
  interior_upper : ∀ i ∈ interiorCells, upper i ≤ 1 - epsilon
  interiorTotal_pos :
    0 < ∑ i ∈ interiorCells, (upper i - lower i)

namespace IntervalMesh

variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

def length (i : Band) : ℝ := M.upper i - M.lower i



def anchor (j : Band) : ℝ :=
  if j ∈ M.interiorCells then M.length j else 0



















/-! ## The exact edge matrix of the sharp continuum kernel block -/

/-- Harmonic mass `∫ dt/t` of a cell. -/
def harmonicMass (i : Band) : ℝ :=
  ∫ t in M.lower i..M.upper i, 1 / t



/-- Continuum center: ordinary length divided by harmonic mass. -/
def center (i : Band) : ℝ := M.length i / M.harmonicMass i



/-- Row-normalized continuum covariance-kernel cell, written using the
removable quotient so the moving-low endpoint is harmless. -/
def normalizedKernelCell (i j : Band) : ℝ :=
  (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) / M.harmonicMass i

/-- Its sharp-conjugate positive graph edge. -/
def sharpKernelEdge (i j : Band) : ℝ :=
  (M.center j / M.length i) *
    ∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t











end IntervalMesh

end Erdos390.Full.ContinuumCellGraph

end

/- Source module: Erdos390.Full.DoubleKernelPrimeQuadrature -/
section


/-!
# Double-index prime quadrature for the Poisson--Dickman kernel

This module performs the two prime-index quadratures needed in the
positive-cell part of Lemma 8.4.  The constants are chosen once, before the
kernel coordinate, ambient scale, or moving endpoints.  The moving-low-cell
estimates are kept for the next layer; no lower endpoint tending to zero is
hidden in the positive-cell theorem below.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.DoubleKernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit
open KernelPrimeQuadrature
open PoissonDickmanKernelBounds
open PositiveCellTransfer

/-- Actual weighted prime-cell operator on the logarithmic coordinate. -/
def primeCellOperator (z : ℝ) (A Y : ℕ) (f : ℝ → ℝ) : ℝ :=
  fullWeightedReciprocalSum f z Y - fullWeightedReciprocalSum f z A

/-- Continuum cell operator with measure `dt/t`. -/
def continuumCellOperator (z : ℝ) (A Y : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ t in realLogCoordinate z (A : ℝ)..realLogCoordinate z (Y : ℝ),
    f t / t

/-- Natural primes in `(A,Y]`. -/
def intervalPrimes (A Y : ℕ) : Finset ℕ :=
  primesUpTo Y \ primesUpTo A















lemma realLogCoordinate_pos_nat {z : ℝ} {X : ℕ}
    (hz : 1 < z) (hX : 2 ≤ X) :
    0 < realLogCoordinate z (X : ℝ) := by
  simpa only [realLogCoordinate, logCoordinate] using
    (logCoordinate_pos (z := z) (X := X) hz hX)

lemma realLogCoordinate_mono_nat {z : ℝ} {A Y : ℕ}
    (hz : 1 < z) (hA : 2 ≤ A) (hAY : A ≤ Y) :
    realLogCoordinate z (A : ℝ) ≤ realLogCoordinate z (Y : ℝ) := by
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hApos : (0 : ℝ) < A := by positivity
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  unfold realLogCoordinate
  exact div_le_div_of_nonneg_right (Real.log_le_log hApos hAYR) hlogz.le



/-- Exact actual double-prime kernel cell. -/
def doublePrimeKernelCell (z : ℝ) (A₁ Y₁ A₂ Y₂ : ℕ) : ℝ :=
  primeCellOperator z A₁ Y₁ (fun s =>
    primeCellOperator z A₂ Y₂ (covarianceKernel s))

/-- The iterated continuum kernel cell, written in the order convenient for
the second prime quadrature. -/
def doubleContinuumKernelCell (z : ℝ) (A₁ Y₁ A₂ Y₂ : ℕ) : ℝ :=
  continuumCellOperator z A₂ Y₂ (fun t =>
    continuumCellOperator z A₁ Y₁ (covarianceKernel t))





/-- Regularized continuum kernel cell, using the removable quotient at the
low endpoint. -/
def regularizedContinuumKernelCell (z : ℝ) (A Y : ℕ) (s : ℝ) : ℝ :=
  ∫ t in realLogCoordinate z (A : ℝ)..realLogCoordinate z (Y : ℝ),
    covarianceKernelQuotient s t















/-! ## Moving-low input cell -/



















/-- Exact arithmetic harmonic mass of a prime cell. -/
def actualCellMass (A Y : ℕ) : ℝ :=
  fullReciprocalSum Y - fullReciprocalSum A

/-- Exact continuum harmonic mass of the corresponding logarithmic cell. -/
def continuumCellMass (z : ℝ) (A Y : ℕ) : ℝ :=
  Real.log (realLogCoordinate z (Y : ℝ)) -
    Real.log (realLogCoordinate z (A : ℝ))

/-- Actual output-row normalization of a double kernel cell. -/
def normalizedDoublePrimeKernelCell
    (z : ℝ) (A₁ Y₁ A₂ Y₂ : ℕ) : ℝ :=
  doublePrimeKernelCell z A₁ Y₁ A₂ Y₂ / actualCellMass A₁ Y₁

/-- Continuum output-row normalization of the same cell. -/
def normalizedDoubleContinuumKernelCell
    (z : ℝ) (A₁ Y₁ A₂ Y₂ : ℕ) : ℝ :=
  doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂ /
    continuumCellMass z A₁ Y₁





end Erdos390.Full.DoubleKernelPrimeQuadrature

end

/- Source module: Erdos390.Full.CanonicalEndpointIntervalMesh -/
section


/-!
# The exact endpoint interval mesh

The cells use the literal natural cutoffs, including the final cutoff
`floor y`.  A selected positive cell supplies the interior anchor.  The
resulting mesh is therefore exactly the one used by endpoint quadrature;
its upper endpoint is not silently replaced by `1`.
-/

open Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Exact logarithmic-coordinate interval mesh of the canonical natural
cutoffs.  The two interior inequalities are the only anchor inputs. -/
def canonicalIntervalMesh
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchorCell : Fin M.cellCount)
    (hInteriorLower : epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M anchorCell) : ℝ))
    (hInteriorUpper :
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M anchorCell) : ℝ) ≤ 1 - epsilon) :
    IntervalMesh epsilon (Fin (M.cellCount + 1)) where
  lower j := realLogCoordinate (y n)
    ((canonicalCertificate M hdelta hn hW S).lower j : ℝ)
  upper j := realLogCoordinate (y n)
    ((canonicalCertificate M hdelta hn hW S).upper j : ℝ)
  lower_pos j := by
    apply realLogCoordinate_pos_nat
    · have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff (Scale.y_pos
        (Nat.zero_lt_of_lt hn)).le).mp hlog
    · exact hWTwo.trans
        (canonicalCertificate_lower_ge_cutoff M hdelta hn hW S j)
  lower_lt_upper j := by
    let E := canonicalCertificate M hdelta hn hW S
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
      every_fullCutoff_cell_has_prime M hW S j
    have hCut : E.lower j < E.upper j := by
      change fullCutoff M n W j.1 < fullCutoff M n W (j.1 + 1)
      exact hpLower.trans_le hpUpper
    have hLowerPos : (0 : ℝ) < (E.lower j : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < W)
        (canonicalCertificate_lower_ge_cutoff M hdelta hn hW S j))
    have hUpperPos : (0 : ℝ) < (E.upper j : ℝ) :=
      hLowerPos.trans (by exact_mod_cast hCut)
    have hlogStrict : Real.log (E.lower j : ℝ) <
        Real.log (E.upper j : ℝ) :=
      Real.strictMonoOn_log
        hLowerPos hUpperPos
        (by exact_mod_cast hCut)
    unfold realLogCoordinate
    exact div_lt_div_of_pos_right hlogStrict (by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num)
        (Real.log_pos (by exact_mod_cast hn)))
  upper_le_one j := by
    let E := canonicalCertificate M hdelta hn hW S
    have hypos : 0 < y n := Scale.y_pos (Nat.zero_lt_of_lt hn)
    have hUpperPos : (0 : ℝ) < (E.upper j : ℝ) := by
      have hLower := canonicalCertificate_lower_ge_cutoff
        M hdelta hn hW S j
      have hle := E.lower_le_upper j
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < W) (hLower.trans hle))
    have hUpperY : (E.upper j : ℝ) ≤ y n := by
      exact (by exact_mod_cast E.upper_le_yNat j :
        (E.upper j : ℝ) ≤ (yNat n : ℝ)) |>.trans
          (Nat.floor_le hypos.le)
    unfold realLogCoordinate
    apply (div_le_iff₀ (Real.log_pos (by
      have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff hypos.le).mp hlog))).2
    simpa only [one_mul] using Real.log_le_log hUpperPos hUpperY
  interiorCells := {positiveBand M anchorCell}
  interior_lower j hj := by
    have hjEq : j = positiveBand M anchorCell := by simpa using hj
    simpa only [hjEq] using hInteriorLower
  interior_upper j hj := by
    have hjEq : j = positiveBand M anchorCell := by simpa using hj
    simpa only [hjEq] using hInteriorUpper
  interiorTotal_pos := by
    simp only [Finset.sum_singleton]
    exact sub_pos.mpr (by
      let E := canonicalCertificate M hdelta hn hW S
      obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
        every_fullCutoff_cell_has_prime M hW S (positiveBand M anchorCell)
      have hCut : E.lower (positiveBand M anchorCell) <
          E.upper (positiveBand M anchorCell) := by
        change fullCutoff M n W (anchorCell.1 + 1) <
          fullCutoff M n W (anchorCell.1 + 1 + 1)
        exact hpLower.trans_le hpUpper
      have hLowerPos : (0 : ℝ) <
          (E.lower (positiveBand M anchorCell) : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < W)
          (canonicalCertificate_lower_ge_cutoff M hdelta hn hW S _))
      have hUpperPos : (0 : ℝ) <
          (E.upper (positiveBand M anchorCell) : ℝ) :=
        hLowerPos.trans (by exact_mod_cast hCut)
      unfold realLogCoordinate
      exact div_lt_div_of_pos_right
        (Real.strictMonoOn_log hLowerPos hUpperPos (by exact_mod_cast hCut))
        (by
          rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
          exact mul_pos (by norm_num)
            (Real.log_pos (by exact_mod_cast hn))))

@[simp] theorem canonicalIntervalMesh_lower
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchorCell : Fin M.cellCount)
    (hInteriorLower hInteriorUpper) (j : Fin (M.cellCount + 1)) :
    (canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
      hInteriorLower hInteriorUpper).lower j =
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower j : ℝ) := rfl

@[simp] theorem canonicalIntervalMesh_upper
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchorCell : Fin M.cellCount)
    (hInteriorLower hInteriorUpper) (j : Fin (M.cellCount + 1)) :
    (canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
      hInteriorLower hInteriorUpper).upper j =
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper j : ℝ) := rfl

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.RegularMeshActualMomentBoundsEventually -/
section


/-!
# Eventual actual-prime moment bounds on the canonical regular mesh

This file discharges the `MomentReady` inputs of
`RegularMeshActualMomentBounds` from the unconditional prime number theorem
quadratures.  The endpoint family is the canonical family of floored powers
of `y`; no continuum mesh, prime-population, or moment estimate is assumed.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeIntervalPartitionConstructor PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The logarithmic coordinate of one explicit natural cutoff. -/
def cutoffCoordinate (n W r : ℕ) : ℝ :=
  realLogCoordinate (y n) (fullCutoff M n W r : ℝ)













/-- Harmonic continuum main term expressed in the actual floored endpoint
coordinates of a positive cell. -/
def positiveContinuumMass (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  Real.log (cutoffCoordinate M n W (k.1 + 2)) -
    Real.log (cutoffCoordinate M n W (k.1 + 1))

/-- First-coordinate continuum main term for the moving low cell. -/
def lowFirstContinuum (n W : ℕ) : ℝ :=
  cutoffCoordinate M n W 1 - realLogCoordinate (y n) (W : ℝ)

/-- Second-coordinate continuum main term for the moving low cell. -/
def lowSecondContinuum (n W : ℕ) : ℝ :=
  (cutoffCoordinate M n W 1 ^ 2 -
    realLogCoordinate (y n) (W : ℝ) ^ 2) / 2

















/-- Endpoint-only inequalities needed to turn the three uniform PNT
quadratures into `MomentReady`.  All displayed endpoints are the actual
floored natural endpoints. -/
structure EndpointMomentBounds (n W : ℕ)
    (Cmass Cfirst Csecond : ℝ) : Prop where
  n_gt_one : 1 < n
  positiveMain : ∀ k : Fin M.cellCount,
    positiveContinuumMass M n W k ≤ 2 * M.ratio
  positiveMassError : ∀ k : Fin M.cellCount,
    5 * Cmass / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3 ≤
      M.ratio
  lowFirstMain : lowFirstContinuum M n W ≤ 3 * delta / 2
  lowFirstError :
    (2 * Cfirst / Real.log (W : ℝ) ^ 3 +
      Cfirst / (2 * Real.log (W : ℝ) ^ 2)) / Real.log (y n) ≤
        delta / 2
  lowSecondMainLower : 5 * delta ^ 2 / 12 ≤
    lowSecondContinuum M n W
  lowSecondMainUpper : lowSecondContinuum M n W ≤
    11 * delta ^ 2 / 12
  lowSecondError :
    3 * Csecond / (Real.log (y n) ^ 2 * Real.log (W : ℝ)) ≤
      delta ^ 2 / 12
  lowMassMain :
    48 + 5 * Cmass / Real.log (W : ℝ) ^ 3 ≤
      Real.log (Real.log (fullCutoff M n W 1 : ℝ)) -
        Real.log (Real.log (W : ℝ))



variable {n W : ℕ}
  (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper











end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.DiagonalPrimeQuadrature -/
section


/-!
# Prime quadrature for the Poisson--Dickman diagonal multiplier

The compressed operator in Lemma 8.4 contains the multiplier `F(t)` in
addition to the double kernel.  This file proves its actual prime-cell
quadrature independently, including the normalization used on the moving
low output row.
-/

open Set

noncomputable section

namespace Erdos390.Full.DiagonalPrimeQuadrature

open MeasureTheory
open PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open PositiveCellTransfer

/-- Actual diagonal prime-cell numerator. -/
def diagonalPrimeCell (z : ℝ) (A Y : ℕ) : ℝ :=
  primeCellOperator z A Y F

/-- Continuum diagonal cell numerator. -/
def diagonalContinuumCell (z : ℝ) (A Y : ℕ) : ℝ :=
  continuumCellOperator z A Y F

/-- Explicit derivative of the diagonal Abel coefficient. -/
def diagonalWeightedAbelDerivative (z x : ℝ) : ℝ :=
  weightedAbelCoefficientDerivative F derivFExtension z x































def normalizedDiagonalPrimeCell (z : ℝ) (A Y : ℕ) : ℝ :=
  diagonalPrimeCell z A Y / actualCellMass A Y

def normalizedDiagonalContinuumCell (z : ℝ) (A Y : ℕ) : ℝ :=
  diagonalContinuumCell z A Y / continuumCellMass z A Y







end Erdos390.Full.DiagonalPrimeQuadrature

end

/- Source module: Erdos390.Full.CompressedArithmeticOperator -/
section


/-!
# The actual compressed arithmetic operator

This file packages the diagonal and double-kernel cells used in the
arithmetic bridge, performs the sharp conjugation, and proves the complete
row aggregation estimate.  The moving low row is not discarded: its
normalization is exactly the one provided by the proved normalized
quadrature modules.

No inverse or spectral gap is an input here.  The output is the explicit
operator error that is fed to the finite graph inverse and then to
`StableInverse`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.CompressedArithmeticOperator

open DoubleKernelPrimeQuadrature DiagonalPrimeQuadrature
open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]

/-- Sharp conjugation of a row-normalized diagonal/kernel matrix.  If `b_j`
is the unscaled band coefficient and `b_j = alpha_j q_j`, this is the output
after division by the output center `alpha_i`. -/
def sharpOperator (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha q : Band → ℝ) (i : Band) : ℝ :=
  diagonal i * q i +
    ∑ j, kernel i j * (alpha j / alpha i) * q j







/-! ## Endpoint-specialized arithmetic and continuum matrices -/

def arithmeticDiagonal (z : ℝ) (lower upper : Band → ℕ)
    (i : Band) : ℝ :=
  normalizedDiagonalPrimeCell z (lower i) (upper i)

def continuumDiagonal (z : ℝ) (lower upper : Band → ℕ)
    (i : Band) : ℝ :=
  normalizedDiagonalContinuumCell z (lower i) (upper i)

def arithmeticKernel (z : ℝ) (lower upper : Band → ℕ)
    (i j : Band) : ℝ :=
  normalizedDoublePrimeKernelCell z
    (lower i) (upper i) (lower j) (upper j)

def continuumKernel (z : ℝ) (lower upper : Band → ℕ)
    (i j : Band) : ℝ :=
  normalizedDoubleContinuumKernelCell z
    (lower i) (upper i) (lower j) (upper j)

def arithmeticSharpOperator (z : ℝ) (lower upper : Band → ℕ)
    (alpha q : Band → ℝ) : Band → ℝ :=
  sharpOperator (arithmeticDiagonal z lower upper)
    (arithmeticKernel z lower upper) alpha q





/-! ## Projection to the actual arithmetic gauge -/



end Erdos390.Full.CompressedArithmeticOperator

end

/- Source module: Erdos390.Full.ContinuumSharpArithmeticTransfer -/
section


/-!
# From normalized arithmetic cells to the continuum graph

The exact sharp continuum matrix differs from its positive graph Laplacian
only by an explicit row residual.  Arithmetic quadrature errors, center
errors, and that residual are aggregated here into one sharp row budget.
No inverse or coercivity statement occurs among the hypotheses.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open CompressedArithmeticOperator
open DickmanBasic

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Harmonic cell average of the diagonal multiplier. -/
def normalizedDiagonalCell (i : Band) : ℝ :=
  (∫ s in M.lower i..M.upper i, F s / s) / M.harmonicMass i

def continuumSharpOperator (q : Band → ℝ) : Band → ℝ :=
  sharpOperator M.normalizedDiagonalCell M.normalizedKernelCell M.center q

/-- Failure of the piecewise-center physical vector to be the exact
continuum null vector.  This is an explicit mesh remainder. -/
def rowResidual (i : Band) : ℝ :=
  M.normalizedDiagonalCell i +
    ∑ j, M.normalizedKernelCell i j * (M.center j / M.center i)







end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full

end

/- Source module: Erdos390.Full.ArithmeticGaugeStableInverse -/
section


/-!
# Stable inversion of the compressed arithmetic operator

The actual sharp arithmetic matrix is projected to its weighted gauge and
compared directly with the positive continuum cell graph.  The graph gap is
obtained from the Dickman kernel; it is not supplied as an inverse or
coercivity hypothesis.  Every arithmetic error is quantified row by row,
including the moving low cell.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.ArithmeticGaugeStableInverse

open CompressedArithmeticOperator
open ContinuumCellGraph
open ContinuumCellGraph.IntervalMesh
open FiniteGraphQuotientInverse
open FiniteGraphStableInverse

variable {Band : Type*} [Fintype Band]

lemma sharpOperator_add
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha q r : Band → ℝ) (i : Band) :
    sharpOperator diagonal kernel alpha (q + r) i =
      sharpOperator diagonal kernel alpha q i +
        sharpOperator diagonal kernel alpha r i := by
  unfold sharpOperator
  simp only [Pi.add_apply]
  have hsum :
      (∑ j, kernel i j * (alpha j / alpha i) * (q j + r j)) =
        (∑ j, kernel i j * (alpha j / alpha i) * q j) +
          ∑ j, kernel i j * (alpha j / alpha i) * r j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

lemma sharpOperator_smul
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha q : Band → ℝ) (c : ℝ) (i : Band) :
    sharpOperator diagonal kernel alpha (c • q) i =
      c * sharpOperator diagonal kernel alpha q i := by
  unfold sharpOperator
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsum :
      (∑ j, kernel i j * (alpha j / alpha i) * (c * q j)) =
        c * ∑ j, kernel i j * (alpha j / alpha i) * q j := by
    calc
      _ = ∑ j, c * (kernel i j * (alpha j / alpha i) * q j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hsum]
  ring

/-- The actual sharp arithmetic matrix, followed by projection to the exact
arithmetic weighted gauge. -/
def projectedSharpLinearMap
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha omega : Band → ℝ)
    (hTotal : (∑ i, omega i) ≠ 0) :
    GaugeSpace omega →ₗ[ℝ] GaugeSpace omega where
  toFun q :=
    ⟨meanProjection omega
        (sharpOperator diagonal kernel alpha (q : Band → ℝ)),
      weighted_sum_meanProjection omega
        (sharpOperator diagonal kernel alpha (q : Band → ℝ)) hTotal⟩
  map_add' q r := by
    apply Subtype.ext
    funext i
    change meanProjection omega
        (sharpOperator diagonal kernel alpha
          ((q : Band → ℝ) + (r : Band → ℝ))) i =
      meanProjection omega
          (sharpOperator diagonal kernel alpha (q : Band → ℝ)) i +
        meanProjection omega
          (sharpOperator diagonal kernel alpha (r : Band → ℝ)) i
    rw [show sharpOperator diagonal kernel alpha
        ((q : Band → ℝ) + (r : Band → ℝ)) =
        sharpOperator diagonal kernel alpha (q : Band → ℝ) +
          sharpOperator diagonal kernel alpha (r : Band → ℝ) by
      funext j
      exact sharpOperator_add diagonal kernel alpha
        (q : Band → ℝ) (r : Band → ℝ) j]
    exact meanProjection_add omega _ _ i
  map_smul' c q := by
    apply Subtype.ext
    funext i
    change meanProjection omega
        (sharpOperator diagonal kernel alpha (c • (q : Band → ℝ))) i =
      c * meanProjection omega
        (sharpOperator diagonal kernel alpha (q : Band → ℝ)) i
    rw [show sharpOperator diagonal kernel alpha
        (c • (q : Band → ℝ)) =
        c • sharpOperator diagonal kernel alpha (q : Band → ℝ) by
      funext j
      exact sharpOperator_smul diagonal kernel alpha
        (q : Band → ℝ) c j]
    exact meanProjection_smul omega c _ i

def projectedSharpCLM
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha omega : Band → ℝ)
    (hTotal : (∑ i, omega i) ≠ 0) :
    GaugeSpace omega →L[ℝ] GaugeSpace omega :=
  (projectedSharpLinearMap diagonal kernel alpha omega hTotal).toContinuousLinearMap





end Erdos390.Full.ArithmeticGaugeStableInverse

end

/- Source module: Erdos390.Full.MovingLowGaugeTransfer -/
section


/-!
# Moving-low arithmetic/continuum gauge transfer

This file isolates the normalization which is delicate at the moving low
cell.  An additive estimate for the arithmetic center is not enough because
the center itself tends to zero.  We first prove a quantitative relative
center estimate from separate estimates for `H` and `H * alpha`.  We then
write the sharp conjugate of the weighted gauge projection exactly and
compare two such projections through their normalized weights
`omega_j = H_j * alpha_j^2`.

No limiting mesh, covariance gap, or inverse is assumed in this module.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.MovingLowGaugeTransfer

open Erdos390.Lemma84
open PositiveCellTransfer
open PrimeSums
open PrimeBandQuadrature
open MovingLowMomentQuadrature

section RelativeCenter

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : ArithmeticBandGeometry.Partition n W Band}









end RelativeCenter

section SharpProjection

variable {Band : Type*} [Fintype Band] [DecidableEq Band]

/-- The sharp projection weight from the paper. -/
def sharpWeight (H alpha : Band → ℝ) (j : Band) : ℝ :=
  H j * alpha j ^ 2

def sharpWeightTotal (H alpha : Band → ℝ) : ℝ :=
  ∑ j, sharpWeight H alpha j

def weightedGaugeProjection (H alpha b : Band → ℝ) (j : Band) : ℝ :=
  b j - alpha j *
    ((∑ k, H k * alpha k * b k) / sharpWeightTotal H alpha)

def scaleByCenter (alpha x : Band → ℝ) (j : Band) : ℝ :=
  alpha j * x j

def unscaleByCenter (alpha x : Band → ℝ) (j : Band) : ℝ :=
  x j / alpha j























end SharpProjection

end Erdos390.Full.MovingLowGaugeTransfer

end

/- Source module: Erdos390.Full.PaperWeightedInverseExport -/
section


/-!
# Export of the sharp inverse in the paper's weighted band norm

The finite graph argument is naturally written after the diagonal change of
variables `b j = alpha j * q j`.  This file records the change of variables
as an exact linear equivalence between the two arithmetic gauges.  It also
proves that the projected raw row-normalized matrix is conjugate to
`projectedSharpLinearMap`.  Consequently an inverse estimate in the ordinary
supremum norm of `q` is literally the paper estimate
`max_j |b_j| / |alpha_j|` for the unscaled band coefficient `b`.

There is no limiting centre and no continuum gauge in this algebraic export.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

open ArithmeticGaugeStableInverse
open CompressedArithmeticOperator
open FiniteGraphQuotientInverse
open FiniteGraphStableInverse
open MovingLowGaugeTransfer

variable {Band : Type*} [Fintype Band]

/-- The weights defining the original arithmetic gauge
`sum_j H_j alpha_j b_j = 0`. -/
def rawGaugeWeight (H alpha : Band → ℝ) (j : Band) : ℝ :=
  H j * alpha j

abbrev RawGaugeSpace (H alpha : Band → ℝ) :=
  GaugeSpace (rawGaugeWeight H alpha)

abbrev SharpGaugeSpace (H alpha : Band → ℝ) :=
  GaugeSpace (sharpWeight H alpha)

/-- Exact scaling equivalence between the sharp gauge and the paper's raw
arithmetic gauge. -/
def scaleGaugeLinearEquiv (H alpha : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0) :
    SharpGaugeSpace H alpha ≃ₗ[ℝ] RawGaugeSpace H alpha where
  toFun q := ⟨fun j ↦ alpha j * q.1 j, by
    change ∑ j, rawGaugeWeight H alpha j * (alpha j * q.1 j) = 0
    rw [← q.2]
    apply Finset.sum_congr rfl
    intro j _
    unfold rawGaugeWeight sharpWeight
    ring⟩
  invFun b := ⟨fun j ↦ b.1 j / alpha j, by
    change ∑ j, sharpWeight H alpha j * (b.1 j / alpha j) = 0
    rw [← b.2]
    apply Finset.sum_congr rfl
    intro j _
    unfold rawGaugeWeight sharpWeight
    field_simp [hAlpha j]⟩
  left_inv q := by
    apply Subtype.ext
    funext j
    simp only
    field_simp [hAlpha j]
  right_inv b := by
    apply Subtype.ext
    funext j
    simp only
    field_simp [hAlpha j]
  map_add' q r := by
    apply Subtype.ext
    funext j
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c q := by
    apply Subtype.ext
    funext j
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp]
theorem scaleGaugeLinearEquiv_apply
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (q : SharpGaugeSpace H alpha) (j : Band) :
    ((scaleGaugeLinearEquiv H alpha hAlpha q : RawGaugeSpace H alpha) :
      Band → ℝ) j = alpha j * q.1 j := rfl

@[simp]
theorem scaleGaugeLinearEquiv_symm_apply
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) (j : Band) :
    (((scaleGaugeLinearEquiv H alpha hAlpha).symm b :
      SharpGaugeSpace H alpha) : Band → ℝ) j =
        b.1 j / alpha j := rfl

/-- The paper's weighted band norm, expressed through the exact gauge
equivalence. -/
def paperSharpNorm (H alpha : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) : ℝ :=
  ‖(scaleGaugeLinearEquiv H alpha hAlpha).symm b‖



/-- The row-normalized matrix before sharp conjugation. -/
def rawOperator (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (b : Band → ℝ) (i : Band) : ℝ :=
  diagonal i * b i + ∑ j, kernel i j * b j





theorem weightedGaugeProjection_mem_rawGauge
    (H alpha x : Band → ℝ)
    (hTotal : sharpWeightTotal H alpha ≠ 0) :
    ∑ i, rawGaugeWeight H alpha i *
        weightedGaugeProjection H alpha x i = 0 := by
  have hden : (∑ j, H j * alpha j ^ 2) ≠ 0 := by
    simpa only [sharpWeightTotal, sharpWeight] using hTotal
  unfold rawGaugeWeight weightedGaugeProjection sharpWeightTotal sharpWeight
  have hsum :
      (∑ i, H i * alpha i *
        (x i - alpha i *
          ((∑ k, H k * alpha k * x k) /
            ∑ j, H j * alpha j ^ 2))) =
      (∑ i, H i * alpha i * x i) -
        (∑ i, H i * alpha i ^ 2) *
          ((∑ k, H k * alpha k * x k) /
            ∑ j, H j * alpha j ^ 2) := by
    calc
      _ = (∑ i, H i * alpha i * x i) -
          ∑ i, (H i * alpha i ^ 2) *
            ((∑ k, H k * alpha k * x k) /
              ∑ j, H j * alpha j ^ 2) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← Finset.sum_mul]
  rw [hsum]
  field_simp [hden]
  ring

lemma rawOperator_add
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (b c : Band → ℝ) :
    rawOperator diagonal kernel (b + c) =
      rawOperator diagonal kernel b + rawOperator diagonal kernel c := by
  funext i
  unfold rawOperator
  simp only [Pi.add_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

lemma rawOperator_smul
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (c : ℝ) (b : Band → ℝ) :
    rawOperator diagonal kernel (c • b) =
      c • rawOperator diagonal kernel b := by
  funext i
  unfold rawOperator
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsum :
      (∑ j, kernel i j * (c * b j)) =
        c * ∑ j, kernel i j * b j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

lemma weightedGaugeProjection_add
    (H alpha x y : Band → ℝ) :
    weightedGaugeProjection H alpha (x + y) =
      weightedGaugeProjection H alpha x +
        weightedGaugeProjection H alpha y := by
  funext i
  unfold weightedGaugeProjection
  simp only [Pi.add_apply]
  have hsum :
      (∑ k, H k * alpha k * (x k + y k)) =
        (∑ k, H k * alpha k * x k) +
          ∑ k, H k * alpha k * y k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  ring

lemma weightedGaugeProjection_smul
    (H alpha : Band → ℝ) (c : ℝ) (x : Band → ℝ) :
    weightedGaugeProjection H alpha (c • x) =
      c • weightedGaugeProjection H alpha x := by
  funext i
  unfold weightedGaugeProjection
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsum :
      (∑ k, H k * alpha k * (c * x k)) =
        c * ∑ k, H k * alpha k * x k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  ring

/-- The projected paper matrix on the original arithmetic gauge. -/
def projectedRawLinearMap
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (H alpha : Band → ℝ)
    (hTotal : sharpWeightTotal H alpha ≠ 0) :
    RawGaugeSpace H alpha →ₗ[ℝ] RawGaugeSpace H alpha where
  toFun b := ⟨weightedGaugeProjection H alpha
      (rawOperator diagonal kernel b.1),
    weightedGaugeProjection_mem_rawGauge H alpha
      (rawOperator diagonal kernel b.1) hTotal⟩
  map_add' b c := by
    apply Subtype.ext
    change weightedGaugeProjection H alpha
        (rawOperator diagonal kernel (b.1 + c.1)) =
      weightedGaugeProjection H alpha (rawOperator diagonal kernel b.1) +
        weightedGaugeProjection H alpha (rawOperator diagonal kernel c.1)
    rw [rawOperator_add, weightedGaugeProjection_add]
  map_smul' c b := by
    apply Subtype.ext
    change weightedGaugeProjection H alpha
        (rawOperator diagonal kernel (c • b.1)) =
      c • weightedGaugeProjection H alpha
        (rawOperator diagonal kernel b.1)
    rw [rawOperator_smul, weightedGaugeProjection_smul]







end Erdos390.Full.PaperWeightedInverseExport

end

/- Source module: Erdos390.Full.PaperCompensatedCoefficientBounds -/
section


/-!
# Actual compensated-prime coefficient bounds for Lemma 8.6

This file specializes the elementary coefficient ledger to the literal
arithmetic prime partition.  The regression vector is an element of the
paper's exact arithmetic gauge

`sum_j H_j * alpha_j * q_j = 0`,

and the compensated coefficient is literally
`c_p = (alpha_{j(p)} - t_p) - q_{j(p)}`.  Thus none of the three norms below
is represented by an abstract array or stored in a certificate.

The sole regression input is the sharp norm estimate produced by the
weighted inverse and the row estimate.  All remaining estimates are derived
from the actual prime sums and the already proved canonical-mesh moment
bounds.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport PrimeSums

noncomputable section

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : Partition n W Band)

/-- The literal bandwise regression coefficient at an actual medium prime. -/
def regressionCoefficient
    (q : RawGaugeSpace P.mass P.center) (p : BandPrime n W) : ℝ :=
  q.1 (P.band p)

/-- The literal post-band-regression prime coefficient from paper Lemma 8.6. -/
def compensatedCoefficient
    (q : RawGaugeSpace P.mass P.center) (p : BandPrime n W) : ℝ :=
  P.deviation p - P.regressionCoefficient q p

/-- `sum_p |q_{j(p)}|/p` on the genuine arithmetic prime band. -/
def regressionL1 (q : RawGaugeSpace P.mass P.center) : ℝ :=
  ∑ p : BandPrime n W,
    (1 / (p.1 : ℝ)) * |P.regressionCoefficient q p|

/-- `sum_p q_{j(p)}^2/p` on the genuine arithmetic prime band. -/
def regressionL2Sq (q : RawGaugeSpace P.mass P.center) : ℝ :=
  ∑ p : BandPrime n W,
    (1 / (p.1 : ℝ)) * (P.regressionCoefficient q p) ^ 2

/-- The paper's actual compensated weighted `L¹` coefficient norm. -/
def compensatedL1 (q : RawGaugeSpace P.mass P.center) : ℝ :=
  ∑ p : BandPrime n W,
    (1 / (p.1 : ℝ)) * |P.compensatedCoefficient q p|

/-- The paper's actual compensated weighted quadratic coefficient norm. -/
def compensatedL2Sq (q : RawGaugeSpace P.mass P.center) : ℝ :=
  ∑ p : BandPrime n W,
    (1 / (p.1 : ℝ)) * (P.compensatedCoefficient q p) ^ 2



theorem center_pos (hn : 1 < n) (j : Band) : 0 < P.center j := by
  have hmass : 0 < P.mass j := P.data.mass_pos j
  change 0 <
    (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * tPrime n p.1) / P.mass j
  apply div_pos
  · apply Finset.sum_pos
    · intro p hp
      exact mul_pos (one_div_pos.mpr (by
          exact_mod_cast (prime_of_mem_primeBand p.2).pos))
        (by
          apply div_pos
          · exact Real.log_pos (by
              exact_mod_cast (prime_of_mem_primeBand p.2).one_lt)
          · rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
            exact mul_pos (by norm_num) (Scale.L_pos hn))
    · obtain ⟨p, hp⟩ := P.fiber_nonempty j
      exact ⟨p, by
        simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
          using hp⟩
  · exact hmass

theorem center_ne_zero (hn : 1 < n) (j : Band) : P.center j ≠ 0 :=
  ne_of_gt (P.center_pos hn j)

/-- The exact arithmetic centre energy is strictly positive.  This uses a
literal nonempty band and the positive harmonic mass and centre of each
actual prime cell; no continuum lower bound is involved. -/
theorem centerEnergy_pos [Nonempty Band] (hn : 1 < n) :
    0 < P.centerEnergy := by
  classical
  unfold ArithmeticBandGeometry.Partition.centerEnergy
    Erdos390.Lemma84.WeightedBandData.centerEnergy
    Erdos390.Lemma84.WeightedBandData.bandNormSq
    Erdos390.Lemma84.WeightedBandData.bandInner
  apply Finset.sum_pos
  · intro j _hj
    exact mul_pos (mul_pos (P.data.mass_pos j) (P.center_pos hn j))
      (P.center_pos hn j)
  · exact Finset.univ_nonempty



















end

end Erdos390.Full.ArithmeticBandGeometry.Partition

end

/- Source module: Erdos390.Full.PaperActualCompensatedRegression -/
section


/-!
# The actual two-stage compensated regression in Lemma 8.6

The objects in this file live on the genuine guard-deleted, tilted finite
probability space from `PaperBridgeFit`.  In particular, the nuisance
coefficient is not an abstract vector satisfying a normal equation: it is
defined by applying the inverse of the proved actual nuisance covariance
operator to the literal covariance vector of the post-band-regression score.

This file proves the exact finite identities used before the analytic
`w^2` comparison: the prime-coefficient expansion, nuisance normal equation,
orthogonality, Schur variance identity, and marked-row decomposition.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerCovariance

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The paper's exact raw arithmetic gauge for the actual bridge partition. -/
abbrev RawBandGauge :=
  RawGaugeSpace B.harmonicMass B.bandCenter

/-- A raw gauge coefficient evaluated at the band of an actual prime. -/
def bandRegressionCoefficient
    (q : B.RawBandGauge) (p : BandPrime B.sampleData.n B.sampleData.W) : ℝ :=
  q.1 (B.partition.band p)

/-- The literal band regression score `sum_j q_j Omega_j`. -/
def bandRegressionScore
    (q : B.RawBandGauge) (m : B.sampleData.Sample) : ℝ :=
  ∑ j : Band, q.1 j * B.bandScore j m

/-- The literal post-band-regression prime coefficient
`c_p = g_p - q_{j(p)}`. -/
def actualCompensatedCoefficient
    (q : B.RawBandGauge) (p : BandPrime B.sampleData.n B.sampleData.W) : ℝ :=
  B.primeDeviation p - B.bandRegressionCoefficient q p

/-- The prime part of the compensated score, before nuisance regression. -/
def postBandPrimeScore
    (q : B.RawBandGauge) (m : B.sampleData.Sample) : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    B.actualCompensatedCoefficient q p *
      valuation p.1 (B.sampleData.value m)











/-- The actual normalized tilted law `ν_{n,ξ}`. -/
abbrev tiltedLaw [Nonempty Head] (xi : B.ParamSpace) :
    FiniteProbability B.sampleData.Sample :=
  B.vectorFamily.scalarFamily.tiltedProbability xi

/-- Coordinatewise covariance of the literal nuisance statistic with an
arbitrary actual finite score. -/
def nuisanceCovarianceVector [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ) : B.NuisanceSpace :=
  (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm
    (fun c ↦ (B.tiltedLaw xi).covariance
      (fun m ↦ B.nuisanceStatistic m c) F)

@[simp]
theorem nuisanceCovarianceVector_apply [Nonempty Head]
    (xi : B.ParamSpace) (F : B.sampleData.Sample → ℝ)
    (c : NuisanceCoord B.HeadIndex) :
    B.nuisanceCovarianceVector xi F c =
      (B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c) F := rfl





/-- The second-stage nuisance coefficient, defined by the actual inverse
`Γ_{ξ,n}^{-1}` and the literal covariance vector. -/
def nuisanceCoefficientOfScore [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) : B.NuisanceSpace :=
  (B.nuisanceCovarianceEquiv xi hgamma hgap).symm
    (B.nuisanceCovarianceVector xi F)







/-- Residual after the actual finite nuisance regression. -/
def nuisanceResidualScore [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (F : B.sampleData.Sample → ℝ) (m : B.sampleData.Sample) : ℝ :=
  F m - inner ℝ (B.nuisanceCoefficientOfScore xi hgamma hgap F)
    (B.nuisanceStatistic m)





/-- The actual paper nuisance coefficient `a_Z` after the band regression. -/
def actualNuisanceCoefficient [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) : B.NuisanceSpace :=
  B.nuisanceCoefficientOfScore xi hgamma hgap (B.postBandPrimeScore q)

/-- The fully compensated score `C_g` from the paper. -/
def actualCompensatedScore [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge) : B.sampleData.Sample → ℝ :=
  B.nuisanceResidualScore xi hgamma hgap (B.postBandPrimeScore q)



















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteProbabilityMixture -/
section


/-!
# Exact finite tagged probability mixtures

The covariance of a mixture is not the mixture of the covariances.  This
module therefore starts one level lower: expectations on a tagged sigma
type are proved to be exact convex combinations.  Common-profile estimates
can then be averaged before any covariance subtraction is performed.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]

/-- The exact probability law on the tagged disjoint union. -/
def sigmaMixture (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c)) :
    FiniteProbability (Sigma Omega) where
  mass x := weight.mass x.1 * (mu x.1).mass x.2
  mass_nonneg x := mul_nonneg (weight.mass_nonneg x.1)
    ((mu x.1).mass_nonneg x.2)
  mass_sum := by
    rw [Fintype.sum_sigma]
    calc
      (∑ c, ∑ x, weight.mass c * (mu c).mass x) =
          ∑ c, weight.mass c * ∑ x, (mu c).mass x := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mul_sum]
      _ = ∑ c, weight.mass c := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [(mu c).mass_sum, mul_one]
      _ = 1 := weight.mass_sum

theorem sigmaMixture_expect
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (F : Sigma Omega → ℝ) :
    (sigmaMixture weight mu).expect F =
      ∑ c, weight.mass c * (mu c).expect (fun x ↦ F ⟨c, x⟩) := by
  unfold sigmaMixture expect
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring





end FiniteProbability

namespace PrimePowerCovariance.BoundedValuationLaw

open ArithmeticModel

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}

/-- Regard the same law as bounded by a larger common endpoint.  All
statistics are definitionally unchanged. -/
def widen {Omega₀ : Type*} [Fintype Omega₀] {M₀ M₁ : ℕ}
    (law : BoundedValuationLaw Omega₀ M₀) (hM : M₀ ≤ M₁) :
    BoundedValuationLaw Omega₀ M₁ where
  probability := law.probability
  value := law.value
  value_pos := law.value_pos
  value_le omega := (law.value_le omega).trans hM

@[simp] theorem widen_probability
    {Omega₀ : Type*} [Fintype Omega₀] {M₀ M₁ : ℕ}
    (law : BoundedValuationLaw Omega₀ M₀) (hM : M₀ ≤ M₁) :
    (widen law hM).probability = law.probability := rfl

@[simp] theorem widen_value
    {Omega₀ : Type*} [Fintype Omega₀] {M₀ M₁ : ℕ}
    (law : BoundedValuationLaw Omega₀ M₀) (hM : M₀ ≤ M₁)
    (omega : Omega₀) :
    (widen law hM).value omega = law.value omega := rfl

/-- A tagged mixture of bounded valuation laws with a common endpoint. -/
def sigmaMixture (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M) :
    BoundedValuationLaw (Sigma Omega) M where
  probability := FiniteProbability.sigmaMixture weight
    (fun c ↦ (law c).probability)
  value x := (law x.1).value x.2
  value_pos x := (law x.1).value_pos x.2
  value_le x := (law x.1).value_le x.2

/-- Tagged mixture for component laws which originally carry different
endpoints, after proof that one common endpoint dominates all of them. -/
def sigmaMixtureVarying
    (endpoint : Cell → ℕ) (common : ℕ)
    (hendpoint : ∀ c, endpoint c ≤ common)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) (endpoint c)) :
    BoundedValuationLaw (Sigma Omega) common :=
  sigmaMixture weight (fun c ↦ widen (law c) (hendpoint c))

@[simp] theorem sigmaMixtureVarying_value
    (endpoint : Cell → ℕ) (common : ℕ)
    (hendpoint : ∀ c, endpoint c ≤ common)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) (endpoint c))
    (x : Sigma Omega) :
    (sigmaMixtureVarying endpoint common hendpoint weight law).value x =
      (law x.1).value x.2 := rfl

@[simp] theorem sigmaMixture_value
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    (x : Sigma Omega) :
    (sigmaMixture weight law).value x = (law x.1).value x.2 := rfl





end PrimePowerCovariance.BoundedValuationLaw

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.FiniteProbabilityMixtureTilt -/
section


/-!
# Exponential tilts of finite tagged mixtures

A global exponential tilt of a finite mixture is not obtained by retaining
the old cell weights.  The exact new weights contain the cell partition
functions.  This file proves that identity before any covariance is formed,
so common-profile estimates can safely be averaged across cells.
-/

open scoped BigOperators

namespace Erdos390.Full
namespace FiniteProbability

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]

/-- Score restricted to one tagged component. -/
def sigmaCellScore (S : Sigma Omega → ℝ) (c : Cell) : Omega c → ℝ :=
  fun x => S ⟨c, x⟩

/-- The partition function of the global tagged law is the convex sum of
the component partition functions. -/
theorem sigmaMixture_expPartition
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) :
    (sigmaMixture weight mu).expPartition S =
      ∑ c, weight.mass c * (mu c).expPartition (sigmaCellScore S c) := by
  rw [expPartition, sigmaMixture_expect]
  rfl

/-- Exact cell weights after globally tilting a tagged mixture. -/
def tiltedSigmaWeight
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (S : Sigma Omega → ℝ) : FiniteProbability Cell where
  mass c := weight.mass c *
    (mu c).expPartition (sigmaCellScore S c) /
      (sigmaMixture weight mu).expPartition S
  mass_nonneg c := div_nonneg
    (mul_nonneg (weight.mass_nonneg c)
      ((mu c).expPartition_pos (sigmaCellScore S c)).le)
    ((sigmaMixture weight mu).expPartition_pos S).le
  mass_sum := by
    rw [← Finset.sum_div, ← sigmaMixture_expPartition]
    exact div_self (ne_of_gt ((sigmaMixture weight mu).expPartition_pos S))













end

end FiniteProbability
end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeCellTiltDecomposition -/
section


/-!
# Exact cell-mixture decomposition of the paper bridge tilt

The analytic marked-cell estimates are stated for uniform probability laws on
individual structured cells and their finite tagged mixtures.  This file proves
the exact identification with the probability law carried by `BridgeData`.
Nothing asymptotic is used: the guard-deleted cells, their actual cardinalities,
the baseline cell masses, and the global partition-function reweighting all
remain literal.

This is also the place where the remaining nuisance tilt is exposed.  After the
medium-prime score has been split off, the physical/head factor is an explicit
second exponential tilt; it is not silently absorbed into the prime fugacity.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteProbability ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

 theorem finiteProbability_ext
    {Omega : Type*} [Fintype Omega]
    {mu nu : FiniteProbability Omega} (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk massMu nonnegMu sumMu =>
      cases nu with
      | mk massNu nonnegNu sumNu =>
          dsimp only at h
          subst massNu
          rfl

/-- The literal normalized baseline masses of the finitely many tagged
head/physical cells. -/
def baselineCellProbability [Nonempty Head] :
    FiniteProbability (Cell Head) where
  mass := B.baseline.normalizedCellMass
  mass_nonneg c := (B.baseline.normalizedCellMass_pos c).le
  mass_sum := B.baseline.normalizedCellMass_sum

@[simp] theorem baselineCellProbability_mass [Nonempty Head]
    (c : Cell Head) :
    B.baselineCellProbability.mass c =
      B.baseline.normalizedCellMass c := rfl

/-- Uniform probability on one *actual guard-deleted* bridge cell. -/
def guardedCellProbability (c : Cell Head) :
    FiniteProbability (B.sampleData.SampleAt c) :=
  uniformOnFinset (B.sampleData.cellFinset c)
    (B.sampleData.cell_nonempty c)

@[simp] theorem guardedCellProbability_mass
    (c : Cell Head) (m : B.sampleData.SampleAt c) :
    (B.guardedCellProbability c).mass m =
      1 / (B.sampleData.cellFinset c).card := rfl

/-- The exact baseline probability law obtained by tagging the individual
uniform guard-deleted cell laws. -/
def baselineSigmaProbability [Nonempty Head] :
    FiniteProbability B.sampleData.Sample :=
  sigmaMixture B.baselineCellProbability B.guardedCellProbability

/-- Pointwise equality between the probability law at parameter zero and the
literal tagged mixture.  This checks the cell cardinality normalization rather
than appealing to an informal "uniform within cells" statement. -/
theorem baselineSigmaProbability_mass_eq [Nonempty Head]
    (m : B.sampleData.Sample) :
    B.baselineSigmaProbability.mass m = (B.tiltedLaw 0).mass m := by
  rcases m with ⟨c, m⟩
  change
    (B.baseline.normalizedCellMass c) *
        (1 / ((B.sampleData.cellFinset c).card : ℝ)) =
      B.vectorFamily.probabilityMass 0 ⟨c, m⟩
  rw [B.probabilityMass_zero]
  unfold BaselineAllocation.normalizedCellMass
    BaselineAllocation.baseWeight BridgeData.q
  have hcard : ((B.sampleData.cellFinset c).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (B.sampleData.cell_nonempty c)
  have hq : B.baseline.totalMass ≠ 0 := by
    exact ne_of_gt B.baseline.totalMass_pos
  simp only [StructuredSampleData.cellOf, Fintype.card_coe]
  field_simp [hcard, hq]

/-- Equality of the actual finite baseline law and the tagged mixture. -/
theorem baselineSigmaProbability_eq_tiltedLaw_zero [Nonempty Head] :
    B.baselineSigmaProbability = B.tiltedLaw 0 := by
  apply finiteProbability_ext
  funext m
  exact B.baselineSigmaProbability_mass_eq m

/-- The actual scalar score divided by the paper scale `L`. -/
def scaledBridgeScore [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) : ℝ :=
  B.vectorFamily.scalarFamily.score m xi / B.L

/-- The medium-prime part of the scaled score. -/
def scaledMediumScore [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    (B.effectivePrimeCoefficient xi p / B.L) *
      valuation p.1 (B.sampleData.value m)

/-- The residual physical/head part of the scaled score. -/
def scaledNuisanceScore [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) : ℝ :=
  inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m) / B.L



/-- The normalized finite-exponential-family law is exactly the exponential
tilt of its normalized baseline probability. -/
theorem tiltedLaw_eq_exponentialTilt_baseline [Nonempty Head]
    (xi : B.ParamSpace) :
    B.tiltedLaw xi =
      (B.baselineSigmaProbability).exponentialTilt
        (B.scaledBridgeScore xi) := by
  apply finiteProbability_ext
  funext m
  have hbase := B.baselineSigmaProbability_mass_eq m
  change B.vectorFamily.probabilityMass xi m =
    B.baselineSigmaProbability.mass m *
        Real.exp (B.scaledBridgeScore xi m) /
      B.baselineSigmaProbability.expPartition
        (B.scaledBridgeScore xi)
  rw [hbase]
  simp only [tiltedLaw, FiniteExponentialFamily.tiltedProbability]
  change B.vectorFamily.probabilityMass xi m =
    B.vectorFamily.probabilityMass 0 m *
        Real.exp (B.scaledBridgeScore xi m) /
      B.baselineSigmaProbability.expPartition
        (B.scaledBridgeScore xi)
  rw [B.probabilityMass_zero m]
  unfold VectorExponentialFamily.probabilityMass
    FiniteExponentialFamily.probabilityMass
    FiniteExponentialFamily.unnormalizedWeight scaledBridgeScore
  have hpart :
      B.baselineSigmaProbability.expPartition
          (B.scaledBridgeScore xi) =
        B.vectorFamily.scalarFamily.partition xi /
          B.vectorFamily.scalarFamily.baseMass := by
    unfold FiniteProbability.expPartition FiniteProbability.expect
    rw [B.baselineSigmaProbability_eq_tiltedLaw_zero]
    simp only [tiltedLaw,
      FiniteExponentialFamily.tiltedProbability,
      FiniteExponentialFamily.probabilityMass]
    have hpartZero : B.vectorFamily.scalarFamily.partition 0 =
        B.vectorFamily.scalarFamily.baseMass := by
      unfold FiniteExponentialFamily.partition
        FiniteExponentialFamily.unnormalizedWeight
        FiniteExponentialFamily.baseMass
      simp
    rw [hpartZero]
    calc
      (∑ x,
          B.vectorFamily.scalarFamily.unnormalizedWeight 0 x /
              B.vectorFamily.scalarFamily.baseMass *
            Real.exp (B.scaledBridgeScore xi x)) =
          (∑ x,
            B.vectorFamily.scalarFamily.unnormalizedWeight xi x) /
              B.vectorFamily.scalarFamily.baseMass := by
        calc
          _ = ∑ x,
              (B.vectorFamily.scalarFamily.unnormalizedWeight 0 x *
                Real.exp (B.scaledBridgeScore xi x)) /
                  B.vectorFamily.scalarFamily.baseMass := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = (∑ x,
              B.vectorFamily.scalarFamily.unnormalizedWeight 0 x *
                Real.exp (B.scaledBridgeScore xi x)) /
                  B.vectorFamily.scalarFamily.baseMass := by
            rw [Finset.sum_div]
          _ = _ := by
            apply congrArg (fun z : ℝ ↦ z /
              B.vectorFamily.scalarFamily.baseMass)
            apply Finset.sum_congr rfl
            intro k hk
            unfold FiniteExponentialFamily.unnormalizedWeight
              scaledBridgeScore
            simp only [map_zero, zero_div, Real.exp_zero, mul_one]
            rfl
      _ = B.vectorFamily.scalarFamily.partition xi /
          B.vectorFamily.scalarFamily.baseMass := by
        rfl
  have hpart' :
      B.baselineSigmaProbability.expPartition
          (fun k => B.vectorFamily.scalarFamily.score k xi / B.L) =
        B.vectorFamily.scalarFamily.partition xi /
          B.vectorFamily.scalarFamily.baseMass := by
    simpa only [scaledBridgeScore] using hpart
  rw [hpart']
  have hbaseMass :
      B.vectorFamily.scalarFamily.baseMass = B.q := by
    simpa only [VectorExponentialFamily.scalarFamily] using
      B.vectorFamily_baseMass
  rw [hbaseMass]
  field_simp [ne_of_gt B.q_pos,
    B.vectorFamily.scalarFamily.partition_ne_zero xi]
  change B.baseline.baseWeight m *
      Real.exp (B.vectorFamily.scalarFamily.score m xi / B.L) =
    B.baseline.baseWeight m *
      Real.exp (B.vectorFamily.scalarFamily.score m xi / B.L)
  rfl





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalBaselineBridge -/
section


/-!
# The canonical baseline inside the literal bridge law

This file identifies the finite-cell logarithmic averages used by the
barycentric construction with the actual conditional physical means and
with the physical moment of the bridge probability law at parameter zero.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit

noncomputable section

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

namespace PaperBridgeFit.BridgeData

/-- The actual coarse conditional physical mean is the literal uniform
average over the corresponding guard-deleted cell.  In particular, it is
independent of the positive baseline mass assigned to that cell. -/
theorem cellPhysicalMean_eq_cellLogMean [Nonempty Head]
    (B : BridgeData Head Band) (c : Cell Head) :
    B.cellPhysicalMean c = cellLogMean B.sampleData c := by
  have hmoment := B.cellPhysicalMean_mul_weight c
  rw [B.nuisanceCoarseBaseline_weight c] at hmoment
  have hsum :
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m) =
        B.baseline.normalizedCellMass c * cellLogMean B.sampleData c := by
    change (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
        B.sampleData.cellOf m = c,
      B.vectorFamily.probabilityMass 0 m * B.physicalScore m) = _
    simp_rw [B.probabilityMass_zero]
    rw [Finset.sum_filter, Fintype.sum_sigma]
    simp only [StructuredSampleData.cellOf]
    rw [Finset.sum_eq_single c]
    · simp only [if_true, BaselineAllocation.baseWeight,
        BaselineAllocation.normalizedCellMass, BridgeData.q,
        BridgeData.physicalScore, StructuredSampleData.value, cellLogMean]
      have hcard :
          (Fintype.card (B.sampleData.SampleAt c) : ℝ) ≠ 0 := by
        exact_mod_cast
          (Nat.ne_of_gt (B.sampleData.sampleAt_card_pos c))
      have hmass : B.baseline.totalMass ≠ 0 :=
        ne_of_gt B.baseline.totalMass_pos
      simp only [StructuredSampleData.cellOf]
      change (∑ m : B.sampleData.SampleAt c,
        (B.baseline.cellMass c / (Fintype.card (B.sampleData.SampleAt c) : ℝ) /
          B.baseline.totalMass) * Real.log ((m.val : ℝ) / B.sampleData.n)) = _
      rw [← Finset.mul_sum]
      field_simp [hcard, hmass]
    · intro c' hc' hne
      simp [hne]
    · intro hc
      exact (hc (Finset.mem_univ c)).elim
  rw [hsum] at hmoment
  exact mul_left_cancel₀ (ne_of_gt
    (B.baseline.normalizedCellMass_pos c)) hmoment







end PaperBridgeFit.BridgeData

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.FiniteTiltCovarianceDomination -/
section


/-!
# Covariance domination under a bounded finite exponential tilt

A bounded tilt need not be close to the baseline in total variation.  It
does, however, dominate the baseline measure by the exact density factor
`exp (-2K)`.  Since variance is the minimum mean-square distance from a
constant, the same factor transfers every covariance quadratic form.  This
is useful for passing a proved finite baseline gap to a whole preselected
tilt box without introducing a fictitious limiting covariance matrix.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

theorem expect_const (mu : FiniteProbability Omega) (c : ℝ) :
    mu.expect (fun _ ↦ c) = c := by
  unfold expect
  rw [← Finset.sum_mul, mu.mass_sum, one_mul]

/-- Mean-square distance from an arbitrary constant is variance plus the
square of the displacement from the mean. -/
theorem expect_sq_sub_const_eq_covariance_add_sq
    (mu : FiniteProbability Omega) (F : Omega → ℝ) (c : ℝ) :
    mu.expect (fun omega ↦ (F omega - c) ^ 2) =
      mu.covariance F F + (mu.expect F - c) ^ 2 := by
  have hfun : (fun omega ↦ (F omega - c) ^ 2) =
      fun omega ↦ F omega * F omega +
        ((-2 * c) * F omega + c ^ 2) := by
    funext omega
    ring
  rw [hfun, mu.expect_add]
  have htail : mu.expect (fun omega ↦ (-2 * c) * F omega + c ^ 2) =
      (-2 * c) * mu.expect F + c ^ 2 := by
    rw [mu.expect_add, mu.expect_smul, mu.expect_const]
  rw [htail]
  unfold covariance
  ring

theorem covariance_self_le_expect_sq_sub_const
    (mu : FiniteProbability Omega) (F : Omega → ℝ) (c : ℝ) :
    mu.covariance F F ≤ mu.expect (fun omega ↦ (F omega - c) ^ 2) := by
  rw [mu.expect_sq_sub_const_eq_covariance_add_sq F c]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Upper bound for the partition function of an absolutely `K`-bounded
score. -/
theorem expPartition_le_exp
    (mu : FiniteProbability Omega) (score : Omega → ℝ) (K : ℝ)
    (hscore : ∀ omega, |score omega| ≤ K) :
    mu.expPartition score ≤ Real.exp K := by
  unfold expPartition expect
  calc
    (∑ omega, mu.mass omega * Real.exp (score omega)) ≤
        ∑ omega, mu.mass omega * Real.exp K := by
      apply Finset.sum_le_sum
      intro omega homega
      apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
      exact Real.exp_le_exp.mpr
        ((le_abs_self (score omega)).trans (hscore omega))
    _ = Real.exp K := by
      rw [← Finset.sum_mul, mu.mass_sum, one_mul]

/-- A bounded exponential tilt dominates every nonnegative expectation by
the pointwise density-ratio factor `exp (-2K)`. -/
theorem exp_neg_two_mul_expect_le_exponentialTilt_expect
    (mu : FiniteProbability Omega) (A score : Omega → ℝ) (K : ℝ)
    (hA : ∀ omega, 0 ≤ A omega)
    (hscore : ∀ omega, |score omega| ≤ K) :
    Real.exp (-2 * K) * mu.expect A ≤
      (mu.exponentialTilt score).expect A := by
  let Z := mu.expPartition score
  let E := mu.expect A
  let numerator := mu.expect (fun omega ↦ A omega * Real.exp (score omega))
  have hE : 0 ≤ E := mu.expect_nonneg A hA
  have hZ : 0 < Z := mu.expPartition_pos score
  have hZupper : Z ≤ Real.exp K := mu.expPartition_le_exp score K hscore
  have hnum : Real.exp (-K) * E ≤ numerator := by
    unfold numerator E expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega homega
    have hexp : Real.exp (-K) ≤ Real.exp (score omega) :=
      Real.exp_le_exp.mpr
        ((neg_le_neg (hscore omega)).trans (neg_abs_le (score omega)))
    calc
      Real.exp (-K) * (mu.mass omega * A omega) =
          mu.mass omega * (A omega * Real.exp (-K)) := by ring
      _ ≤ mu.mass omega * (A omega * Real.exp (score omega)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (hA omega))
          (mu.mass_nonneg omega)
  rw [mu.exponentialTilt_expect_eq A score]
  change Real.exp (-2 * K) * E ≤ numerator / Z
  calc
    Real.exp (-2 * K) * E =
        (Real.exp (-K) * E) / Real.exp K := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      rw [show Real.exp (-2 * K) =
          Real.exp (-K) * Real.exp (-K) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
    _ ≤ (Real.exp (-K) * E) / Z := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (Real.exp_pos _).le hE) hZ hZupper
    _ ≤ numerator / Z := by
      exact div_le_div_of_nonneg_right hnum hZ.le

/-- Every covariance quadratic form survives a bounded tilt with the same
exact density-ratio factor. -/
theorem exp_neg_two_mul_covariance_self_le_exponentialTilt
    (mu : FiniteProbability Omega) (F score : Omega → ℝ) (K : ℝ)
    (hscore : ∀ omega, |score omega| ≤ K) :
    Real.exp (-2 * K) * mu.covariance F F ≤
      (mu.exponentialTilt score).covariance F F := by
  let nu := mu.exponentialTilt score
  let c := nu.expect F
  have hdom := mu.exp_neg_two_mul_expect_le_exponentialTilt_expect
    (fun omega ↦ (F omega - c) ^ 2) score K
    (fun omega ↦ sq_nonneg _) hscore
  have hmin := mu.covariance_self_le_expect_sq_sub_const F c
  have hfactor : 0 ≤ Real.exp (-2 * K) := (Real.exp_pos _).le
  calc
    Real.exp (-2 * K) * mu.covariance F F ≤
        Real.exp (-2 * K) *
          mu.expect (fun omega ↦ (F omega - c) ^ 2) :=
      mul_le_mul_of_nonneg_left hmin hfactor
    _ ≤ nu.expect (fun omega ↦ (F omega - c) ^ 2) := hdom
    _ = nu.covariance F F := by
      rw [nu.expect_sq_sub_const_eq_covariance_add_sq F c]
      simp only [c, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, add_zero]

end FiniteProbability

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.TwoLocalRestorationBound -/
section


/-!
# Quantitative error of the exact two-local restoration

This file bounds every nonconstant term in the exact `N_{r,s}` numerator
using the arbitrary-modulus reciprocal fallback.  The result retains the
paper's weighted coefficient tails in both local coordinates; in particular,
it does not replace them by the cardinality of the exponent cutoff.
-/

open scoped BigOperators

namespace Erdos390.Full.TwoLocalRestorationBound

open ArithmeticModel FiniteProbability LocalFugacity LocalFugacityBounds
open OmittedTiltPairChamber

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- The exact restored numerator `N_{r,s}` under an arbitrary finite law. -/
def pairRestoredNumerator (nu : FiniteProbability Omega)
    (value : Omega → ℕ) (p q Ap Aq : ℕ) (etaP etaQ L : ℝ)
    (r s : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 0 Ap, ∑ b ∈ Finset.Icc 0 Aq,
    coefficient (Real.exp (etaP / L)) a *
      coefficient (Real.exp (etaQ / L)) b *
        nu.expect (fun omega ↦
          divInd (pairPower p q (max r a) (max s b)) (value omega))

/-- The explicit reciprocal majorant for the nonconstant restoration
terms. -/
def pairRestorationError (p q Ap Aq r s : ℕ)
    (etaP etaQ L G : ℝ) : ℝ :=
  G * coefficientTail p Ap r etaP L * (1 / (q : ℝ) ^ s) +
  G * (1 / (p : ℝ) ^ r) * coefficientTail q Aq s etaQ L +
  G * coefficientTail p Ap r etaP L * coefficientTail q Aq s etaQ L



















end

end Erdos390.Full.TwoLocalRestorationBound

end

/- Source module: Erdos390.Full.PaperTwoLocalRestorationBound -/
section


/-!
# Paper-scale stability of the two-local normalizer

The exact restoration quotient is useful only after its denominator is shown
uniformly away from zero.  This file performs that quantifier step at the
actual paper scale.  The fallback density-ratio constant is first bounded by
a fixed `B,W,c` ceiling, and the two coefficient tails then tend uniformly to
zero over the moving prime band.
-/

open Filter Topology

namespace Erdos390.Full.PaperTwoLocalRestorationBound

open ArithmeticModel Scale LocalFugacityBounds PaperValuationCutoff
open ValuationCutoff
open TwoLocalRestorationBound

noncomputable section

/-- The exact reciprocal-event constant produced by the arbitrary-modulus
omitted-tilt fallback at the paper endpoint. -/
def paperPairFallbackConstant (B C c : ℝ) (W n : ℕ) : ℝ :=
  Real.exp (2 * ((B / L n) *
    (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ)))) / c

/-- A fixed ceiling for the preceding constant. -/
def paperPairFallbackCeiling (B c : ℝ) (W : ℕ) : ℝ :=
  Real.exp (4 * B / Real.log (W : ℝ)) / c









end

end Erdos390.Full.PaperTwoLocalRestorationBound

end

/- Source module: Erdos390.Full.FullTiltPairChamber -/
section


/-!
# Full valuation tilt in the two-prime four-mark chamber

This is the paper-facing closure of the two-local restoration.  It combines

* the actual structured-cell omitted-score four-mark estimate,
* the exact `N_{r,s}/N_{0,0}` restoration identity,
* the arbitrary-modulus reciprocal fallback for every restoration term, and
* the uniform lower bound for the exact normalizer.

The conclusion concerns the genuine full valuation tilt over the genuine
structured cell.  No covariance estimate or analytic transfer is assumed.
-/

open Filter Topology

namespace Erdos390.Full.FullTiltPairChamber

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination ValuationCutoff
open PaperScaleMarkedCell OmittedTiltPairChamber OmittedTiltFallback
open TwoLocalRestoration TwoLocalPairRestoration
open TwoLocalRestorationBound PaperTwoLocalRestorationBound

noncomputable section

/-- The fixed cell-density constant used by the arbitrary-modulus fallback. -/
def pairFallbackDensity (H : Pattern) (A C : ℝ) : ℝ :=
  paperCellDensity H A C / (2 * C)





/-- The explicit full-tilt error ledger.  The first and third terms are the
two-local restoration errors; the middle term is the sharp omitted-score
four-mark error. -/
def fullPairChamberError (H : Pattern) (A C B : ℝ) (W n p q r s : ℕ)
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ) : ℝ :=
  let c := pairFallbackDensity H A C
  let G := paperPairFallbackConstant B C c W n
  let Ap := valuationCutoff p (physicalBound C n)
  let Aq := valuationCutoff q (physicalBound C n)
  2 * (pairRestorationError p q Ap Aq r s (eta p) (eta q) (L n) G +
    epsilon n / (pairPower p q r s : ℝ) +
    |paperDivisibilityMain n (pairPower p q r s)| *
      pairRestorationError p q Ap Aq 0 0 (eta p) (eta q) (L n) G)







end

end Erdos390.Full.FullTiltPairChamber

end

/- Source module: Erdos390.Full.DickmanFourMarkProductKernel -/
section


/-!
# The four-mark Dickman product kernel

The four-mark chamber in the proof of Lemma 7.5 uses the normalized
Dickman profile

`F x = rho (U - x) / rho U`

on the full simplex `x, z >= 0`, `x + z <= 4`.  The local product estimate
in `DickmanBasic` covers the unit square by differentiating the actual
method-of-steps solution near the origin.  This file extends that estimate
to the whole four-mark simplex using the globally proved one-Lipschitz
bound for `rho` on `[0,5]`.  In particular, no `C^{1,1}` hypothesis and no
tilt-box parameter occurs in the statement or proof.
-/

open Set

noncomputable section

namespace Erdos390.Full.DickmanFourMarkProductKernel

open DickmanBasic FriableAsymptotic

/-- The paper's four-mark profile `h_U`, named explicitly for statement
matching.  It is definitionally the `F` constructed in `DickmanBasic`. -/
def fourMarkProfile (x : ℝ) : ℝ := rho (U - x) / rho U

@[simp] theorem fourMarkProfile_eq_F (x : ℝ) : fourMarkProfile x = F x := rfl

@[simp] theorem fourMarkProfile_zero : fourMarkProfile 0 = 1 := by
  simp [fourMarkProfile, rho_U_ne_zero]

/-- Positivity and the uniform absolute bound for the actual normalized
Dickman profile throughout the complete four-mark range. -/
lemma fourMarkProfile_pos_and_abs_le {x : ℝ} (hx0 : 0 ≤ x) (hx4 : x ≤ 4) :
    0 < fourMarkProfile x ∧ |fourMarkProfile x| ≤ 1 / rho U := by
  have harg0 : 0 ≤ U - x := by
    norm_num [U] at hx4 ⊢
    linarith
  have harg5 : U - x ≤ 5 := by
    norm_num [U] at hx0 ⊢
    linarith
  have hrpos : 0 < rho (U - x) := rho_pos_on_zero_five harg0 harg5
  have hrle : rho (U - x) ≤ 1 := rho_le_one_of_le_five harg5
  have hrU : 0 < rho U := rho_U_pos
  constructor
  · exact div_pos hrpos hrU
  · unfold fourMarkProfile
    rw [abs_of_pos (div_pos hrpos hrU)]
    exact (div_le_div_iff_of_pos_right hrU).2 hrle

/-- The normalized four-mark profile is `1 / rho U`-Lipschitz on the
ordered interval `[0,4]`.  This includes the Dickman kink crossed near the
far end of that interval; the proof uses the integral Lipschitz theorem,
not differentiability at the kink. -/
lemma fourMarkProfile_lipschitz {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) :
    |fourMarkProfile b - fourMarkProfile a| ≤
      (1 / rho U) * (b - a) := by
  have hargOrder : U - b ≤ U - a := by linarith
  have hargTop : U - a ≤ 5 := by
    norm_num [U] at ha0 ⊢
    linarith
  have hrho := rho_lipschitz_of_le_five hargOrder hargTop
  have hrU : 0 < rho U := rho_U_pos
  rw [fourMarkProfile, fourMarkProfile]
  rw [div_sub_div_same]
  rw [abs_div, abs_of_pos hrU]
  have hdiff : (U - a) - (U - b) = b - a := by ring
  rw [hdiff] at hrho
  calc
    |rho (U - b) - rho (U - a)| / rho U
        = |rho (U - a) - rho (U - b)| / rho U := by
            rw [abs_sub_comm]
    _ ≤ (b - a) / rho U := (div_le_div_iff_of_pos_right hrU).2 hrho
    _ = (1 / rho U) * (b - a) := by ring

/-- **Box-independent four-mark Dickman product-kernel bound.**

This is the precise analytic sublemma used in the four-mark chamber of
paper Lemma 7.5.  The constant is chosen solely from the already-constructed
Dickman profile at the fixed parameter `U`; there are no tilt radius `B`,
prime cutoff `W`, or asymptotic parameters in either the quantifiers or the
proof. -/
theorem exists_boxIndependent_fourMark_productKernel_bound :
    ∃ C_K : ℝ, 0 < C_K ∧
      ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
        |fourMarkProfile (x + z) -
            fourMarkProfile x * fourMarkProfile z| ≤ C_K * x * z := by
  obtain ⟨C₀, hC₀pos, hlocal⟩ := kernel_product_bound
  let R : ℝ := 1 / rho U
  have hRpos : 0 < R := by
    dsimp [R]
    exact one_div_pos.mpr rho_U_pos
  let C_K : ℝ := C₀ + R + R * R + 1
  have hCKpos : 0 < C_K := by
    dsimp [C_K]
    nlinarith [mul_pos hRpos hRpos]
  refine ⟨C_K, hCKpos, ?_⟩
  intro x z hx0 hz0 hxz4
  have hx4 : x ≤ 4 := by linarith
  have hz4 : z ≤ 4 := by linarith
  have hxz0 : 0 ≤ x + z := add_nonneg hx0 hz0
  have hFx := fourMarkProfile_pos_and_abs_le hx0 hx4
  have hFz := fourMarkProfile_pos_and_abs_le hz0 hz4
  have hFxz := fourMarkProfile_pos_and_abs_le hxz0 hxz4
  by_cases hx1 : x ≤ 1
  · by_cases hz1 : z ≤ 1
    · have hsmall := hlocal x ⟨hx0, hx1⟩ z ⟨hz0, hz1⟩
      rw [← fourMarkProfile_eq_F, ← fourMarkProfile_eq_F,
        ← fourMarkProfile_eq_F] at hsmall
      exact hsmall.trans (by
        have hCdom : C₀ ≤ C_K := by
          dsimp [C_K]
          nlinarith [hRpos]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCdom hx0) hz0)
    · have hz1' : 1 < z := lt_of_not_ge hz1
      have hLipShift := fourMarkProfile_lipschitz hz0
        (show z ≤ x + z by linarith)
      have hLipZero := fourMarkProfile_lipschitz (a := 0) (b := x)
        (by norm_num) hx0
      have hdecomp :
          fourMarkProfile (x + z) - fourMarkProfile x * fourMarkProfile z =
            (fourMarkProfile (x + z) - fourMarkProfile z) +
              fourMarkProfile z * (1 - fourMarkProfile x) := by ring
      rw [hdecomp]
      calc
        |(fourMarkProfile (x + z) - fourMarkProfile z) +
            fourMarkProfile z * (1 - fourMarkProfile x)| ≤
            |fourMarkProfile (x + z) - fourMarkProfile z| +
              |fourMarkProfile z * (1 - fourMarkProfile x)| := abs_add_le _ _
        _ ≤ R * x + R * (R * x) := by
          apply add_le_add
          · simpa [R, add_sub_cancel_left] using hLipShift
          · rw [abs_mul]
            have hzeroDiff : |1 - fourMarkProfile x| ≤ R * x := by
              rw [← fourMarkProfile_zero]
              simpa [R, abs_sub_comm] using hLipZero
            exact mul_le_mul hFz.2 hzeroDiff (abs_nonneg _) hRpos.le
        _ ≤ C_K * x * z := by
          have hCoeff : R + R * R ≤ C_K := by
            dsimp [C_K]
            linarith [hC₀pos]
          calc
            R * x + R * (R * x) = (R + R * R) * x := by ring
            _ ≤ C_K * x := mul_le_mul_of_nonneg_right hCoeff hx0
            _ ≤ (C_K * x) * z := by
              have h := mul_le_mul_of_nonneg_left hz1'.le
                (mul_nonneg hCKpos.le hx0)
              simpa using h
            _ = C_K * x * z := rfl
  · have hx1' : 1 < x := lt_of_not_ge hx1
    by_cases hz1 : z ≤ 1
    · have hLipShift := fourMarkProfile_lipschitz hx0
        (show x ≤ x + z by linarith)
      have hLipZero := fourMarkProfile_lipschitz (a := 0) (b := z)
        (by norm_num) hz0
      have hdecomp :
          fourMarkProfile (x + z) - fourMarkProfile x * fourMarkProfile z =
            (fourMarkProfile (x + z) - fourMarkProfile x) +
              fourMarkProfile x * (1 - fourMarkProfile z) := by ring
      rw [hdecomp]
      calc
        |(fourMarkProfile (x + z) - fourMarkProfile x) +
            fourMarkProfile x * (1 - fourMarkProfile z)| ≤
            |fourMarkProfile (x + z) - fourMarkProfile x| +
              |fourMarkProfile x * (1 - fourMarkProfile z)| := abs_add_le _ _
        _ ≤ R * z + R * (R * z) := by
          apply add_le_add
          · simpa [R, add_sub_cancel_left] using hLipShift
          · rw [abs_mul]
            have hzeroDiff : |1 - fourMarkProfile z| ≤ R * z := by
              rw [← fourMarkProfile_zero]
              simpa [R, abs_sub_comm] using hLipZero
            exact mul_le_mul hFx.2 hzeroDiff (abs_nonneg _) hRpos.le
        _ ≤ C_K * x * z := by
          have hCoeff : R + R * R ≤ C_K := by
            dsimp [C_K]
            linarith [hC₀pos]
          calc
            R * z + R * (R * z) = (R + R * R) * z := by ring
            _ ≤ C_K * z := mul_le_mul_of_nonneg_right hCoeff hz0
            _ ≤ (C_K * x) * z := by
              apply mul_le_mul_of_nonneg_right _ hz0
              nlinarith [hCKpos]
            _ = C_K * x * z := by ring
    · have hz1' : 1 < z := lt_of_not_ge hz1
      calc
        |fourMarkProfile (x + z) -
            fourMarkProfile x * fourMarkProfile z| ≤
            |fourMarkProfile (x + z)| +
              |fourMarkProfile x * fourMarkProfile z| := abs_sub _ _
        _ ≤ R + R * R := by
          apply add_le_add hFxz.2
          rw [abs_mul]
          exact mul_le_mul hFx.2 hFz.2 (abs_nonneg _) hRpos.le
        _ ≤ C_K * x * z := by
          have hCoeff : R + R * R ≤ C_K := by
            dsimp [C_K]
            linarith [hC₀pos]
          have hxy : 1 ≤ x * z := by nlinarith
          calc
            R + R * R ≤ C_K := hCoeff
            _ ≤ C_K * (x * z) := by
              nlinarith [hCKpos]
            _ = C_K * x * z := by ring

/-- A fixed witness for the four-mark product-kernel constant.  Naming the
witness makes the dependency order formal: later prime cutoffs may depend on
this number, whereas the finite head-pattern family is selected only after
the cutoff. -/
noncomputable def boxIndependentFourMarkKernelConstant : ℝ :=
  Classical.choose exists_boxIndependent_fourMark_productKernel_bound







end Erdos390.Full.DickmanFourMarkProductKernel

end

/- Source module: Erdos390.Full.StructuredCellValuationLaw -/
section


/-!
# Actual valuation law on a structured smooth cell

This file packages the literal subtype of a structured cell, its genuine
finite probability mass, and the coercion to the sampled positive integer as
one `BoundedValuationLaw`.  It removes a model-interface gap: the prime-power
covariance theorems can now be instantiated directly with the same tilted law
used by the marked-cell asymptotics.
-/

namespace Erdos390.Full.StructuredCellValuationLaw

open ArithmeticModel StructuredCells FiniteProbability
open PrimePowerCovariance ValuationScoreDomination

noncomputable section

/-- Any probability law on the literal structured-cell subtype is an actual
positive integer-valued law bounded by the cell's upper endpoint. -/
def ofProbability (H : HeadPattern.Pattern) (lo hi z : Nat)
    (mu : FiniteProbability (structuredCell H lo hi z)) :
    BoundedValuationLaw (structuredCell H lo hi z) hi where
  probability := mu
  value := fun m => (m : Nat)
  value_pos := by
    intro m
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  value_le := by
    intro m
    exact (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1

@[simp] theorem ofProbability_probability
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (mu : FiniteProbability (structuredCell H lo hi z)) :
    (ofProbability H lo hi z mu).probability = mu := rfl

@[simp] theorem ofProbability_value
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (mu : FiniteProbability (structuredCell H lo hi z))
    (m : structuredCell H lo hi z) :
    (ofProbability H lo hi z mu).value m = (m : Nat) := rfl

/-- The genuine full valuation tilt on a nonempty structured cell, packaged
as the bounded valuation law used by the prime-power covariance ledger. -/
def valuationTilt
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) :
    BoundedValuationLaw (structuredCell H lo hi z) hi :=
  ofProbability H lo hi z
    ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
      (fun m => valuationScore P eta L m))

@[simp] theorem valuationTilt_probability
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) :
    (valuationTilt H lo hi z hS P eta L).probability =
      (uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m) := rfl

@[simp] theorem valuationTilt_value
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real)
    (m : structuredCell H lo hi z) :
    (valuationTilt H lo hi z hS P eta L).value m = (m : Nat) := rfl

@[simp] theorem valuationTilt_I
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p : Nat) :
    (valuationTilt H lo hi z hS P eta L).I p =
      fun m : structuredCell H lo hi z => divInd p (m : Nat) := rfl

@[simp] theorem valuationTilt_V
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p : Nat) :
    (valuationTilt H lo hi z hS P eta L).V p =
      fun m : structuredCell H lo hi z => valuation p (m : Nat) := rfl

@[simp] theorem valuationTilt_J
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p : Nat) :
    (valuationTilt H lo hi z hS P eta L).J p =
      fun m : structuredCell H lo hi z => higherValuation p (m : Nat) := rfl

@[simp] theorem valuationTilt_covII
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p q : Nat) :
    (valuationTilt H lo hi z hS P eta L).covII p q =
      ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m)).covariance
          (fun m => divInd p (m : Nat))
          (fun m => divInd q (m : Nat)) := rfl

@[simp] theorem valuationTilt_covJI
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p q : Nat) :
    (valuationTilt H lo hi z hS P eta L).covJI p q =
      ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m)).covariance
          (fun m => higherValuation p (m : Nat))
          (fun m => divInd q (m : Nat)) := rfl

@[simp] theorem valuationTilt_covIJ
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p q : Nat) :
    (valuationTilt H lo hi z hS P eta L).covIJ p q =
      ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m)).covariance
          (fun m => divInd p (m : Nat))
          (fun m => higherValuation q (m : Nat)) := rfl

@[simp] theorem valuationTilt_covJJ
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p q : Nat) :
    (valuationTilt H lo hi z hS P eta L).covJJ p q =
      ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m)).covariance
          (fun m => higherValuation p (m : Nat))
          (fun m => higherValuation q (m : Nat)) := rfl

@[simp] theorem valuationTilt_covVV
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p q : Nat) :
    (valuationTilt H lo hi z hS P eta L).covVV p q =
      ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m)).covariance
          (fun m => valuation p (m : Nat))
          (fun m => valuation q (m : Nat)) := rfl

end

end Erdos390.Full.StructuredCellValuationLaw

end

/- Source module: Erdos390.Full.PaperPrimePowerChamberError -/
section


/-!
# Explicit chamber-error majorants for prime-power aggregation

This file replaces the nested restoration ledger by one scalar remainder at
the natural product-reciprocal scale.  The scalar is explicit, uniform over
all moving primes and exponents, and retains the vanishing omitted-score and
`1 / log n` factors needed before the harmonic prime sum is taken.
-/

namespace Erdos390.Full.PaperPrimePowerChamberError

open ArithmeticModel Scale HeadPattern
open OmittedTiltPairChamber FullTiltPairChamber
open LocalFugacityBounds TwoLocalRestorationBound
open PaperTwoLocalRestorationBound PaperScaleMarkedCell
open FullTiltPrimePowerCovariance

noncomputable section

/-- The uniform pointwise coefficient-tail scalar. -/
def coefficientScale (B : ℝ) (W n : ℕ) : ℝ :=
  (2 * B / L n) * Real.exp (2 * B / Real.log (W : ℝ))

/-- The common reciprocal weight for an exponent pair. -/
def pairWeight (p q r s : ℕ) : ℝ :=
  (((r : ℝ) + 1) * ((s : ℝ) + 1)) /
    ((p : ℝ) ^ r * (q : ℝ) ^ s)

/-- The one-prime factor of `pairWeight`. -/
def singleWeight (p r : ℕ) : ℝ :=
  ((r : ℝ) + 1) / (p : ℝ) ^ r







/-- Scalar bounding every local-restoration numerator error. -/
def localRestorationScale (G k : ℝ) : ℝ :=
  G * (2 * k + k ^ 2)

/-- Scalar bounding one restored marked probability. -/
def pairProbabilityScale (epsilon G k : ℝ) : ℝ :=
  2 * (localRestorationScale G k + epsilon +
    (1 / DickmanBasic.rho DickmanBasic.U) * localRestorationScale G k)

/-- Scalar bounding the covariance perturbation formed from one joint and
two marginal probability errors. -/
def pairCovarianceScale (E : ℝ) : ℝ :=
  E * (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) + E ^ 2

/-- One remainder large enough for the `JI`, `IJ`, `JJ`, and diagonal
pointwise inputs of the finite aggregation theorem. -/
def aggregateChamberScale (epsilon G k : ℝ) : ℝ :=
  2 * pairCovarianceScale (pairProbabilityScale epsilon G k) +
    pairProbabilityScale epsilon G k





















end

end Erdos390.Full.PaperPrimePowerChamberError

end

/- Source module: Erdos390.Full.PaperPrimePowerTailLedger -/
section


/-!
# Actual prime-power tail and endpoint ledgers

This module closes the finite arithmetic part of the beyond-four-mark
argument in paper Lemma 7.5.  The exponent sets are the actual logarithmic
valuation cutoffs, the primes belong to the actual finite band cut off by
`yNat`, and the four-mark boundary is the literal integer inequality
`yNat n ^ 4 < D`.  No asymptotic `O` notation is used in the statements.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerTailLedger

open ArithmeticModel Scale ValuationCutoff PaperValuationCutoff

noncomputable section

/-- Exponents in the `J_p I_q` orientation whose forced modulus is beyond
the actual four-mark range. -/
def jiBeyondFour (n p q A : ℕ) : Finset ℕ :=
  (highExponents A).filter (fun r ↦ yNat n ^ 4 < p ^ r * q)

/-- The transposed `I_p J_q` tail. -/
def ijBeyondFour (n p q A : ℕ) : Finset ℕ :=
  (highExponents A).filter (fun s ↦ yNat n ^ 4 < p * q ^ s)

/-- Exponent pairs in the `J_p J_q` orientation beyond the actual
four-mark range. -/
def jjBeyondFour (n p q A B : ℕ) : Finset (ℕ × ℕ) :=
  ((highExponents A).product (highExponents B)).filter
    (fun rs ↦ yNat n ^ 4 < p ^ rs.1 * q ^ rs.2)

/-- The diagonal high-power tail beyond four marks. -/
def diagonalBeyondFour (n p A : ℕ) : Finset ℕ :=
  (highExponents A).filter (fun r ↦ yNat n ^ 4 < p ^ r)





































/-! ## Literal endpoint multiplicities -/







/-! ## Actual logarithmic cutoffs and paper-scale ledgers -/

/-- The exact exponent cutoff for one prime in the physical interval. -/
def actualExponentCutoff (C : ℝ) (n p : ℕ) : ℕ :=
  valuationCutoff p (physicalBound C n)

/-- The fixed cutoff coefficient `2 / log W`. -/
def cutoffScale (W : ℕ) : ℝ := 2 / Real.log (W : ℝ)





















end

end Erdos390.Full.PaperPrimePowerTailLedger

end

/- Source module: Erdos390.Full.PaperPrimePowerPointwise -/
section


/-!
# Literal-chamber pointwise prime-power estimates

This file performs the deterministic splice used in Lemma 7.5.  Inside the
literal arithmetic chamber `p^r q^s <= yNat n ^ 4` it uses the sharp
Dickman covariance term and the explicit restoration ledger.  Outside the
chamber it records the uniform reciprocal fallback as a named residual.
-/

namespace Erdos390.Full.PaperPrimePowerPointwise

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open OmittedTiltPairChamber
open FullTiltPairChamber FullTiltPrimePowerCovariance
open FullTiltPrimePowerActualChamber FullTiltPrimePowerFallback
open PaperPrimePowerChamberError

noncomputable section

/-- The literal beyond-four covariance residual. -/
def covarianceTail (G : ℝ) (n p q r s : ℕ) : ℝ :=
  if pairPower p q r s ≤ yNat n ^ 4 then 0
  else (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s)

/-- The literal beyond-four one-prime probability residual. -/
def probabilityTail (G : ℝ) (n p r : ℕ) : ℝ :=
  if p ^ r ≤ yNat n ^ 4 then 0 else G / (p : ℝ) ^ r











end

end Erdos390.Full.PaperPrimePowerPointwise

end

/- Source module: Erdos390.Full.PaperPrimePowerPairAggregation -/
section


/-!
# From actual prime-power pairs to a paper prime row

This file performs the finite aggregation that follows the pointwise
two-local estimates in Lemma 7.5.  Its inputs are covariances and moments of
the genuine divisor-indicator columns of an actual `BoundedValuationLaw`.
The preceding logarithmic-cutoff module makes every exponent range literal.

The factors `8`, `64`, and `quadraticHalfMass` are obtained from the proved
geometric series, rather than hidden in an `O`-constant.  A single universal
aggregation constant then feeds the already formalized paper-band row
contraction.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerPairAggregation

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCutoffCovariance LocalFugacityBounds
open ValuationCutoff
open PrimeSums
open PaperPrimePowerRow

noncomputable section

/-- One constant dominating all four finite geometric aggregations. -/
def pairAggregationConstant : ℝ := 64 + quadraticHalfMass









namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)











end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerPairAggregation

end

/- Source module: Erdos390.Full.PaperPrimePowerFourDisplays -/
section


/-!
# The four pointwise displays of Lemma 7.5

This file is the exact algebraic specialization of the generic actual-law
splice to `JI`, `IJ`, `JJ`, and the diagonal second-moment input.  One main
constant and one chamber remainder dominate all four orientations.
-/

namespace Erdos390.Full.PaperPrimePowerFourDisplays

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PaperPrimePowerChamberError PaperPrimePowerPointwise

noncomputable section

/-- The box-independent coefficient common to all four displays. -/
def primePowerMainConstant (C_K : ℝ) : ℝ :=
  2 * C_K + 1 / DickmanBasic.rho DickmanBasic.U

/-- The common chamber remainder used in all four displays. -/
def primePowerChamberRemainder (epsilon G₀ k : ℝ) : ℝ :=
  aggregateChamberScale epsilon G₀ k

/-- Literal outside-chamber residual in the `JI` orientation. -/
def eJI (G : ℝ) (n p q r : ℕ) : ℝ := covarianceTail G n p q r 1

/-- Literal outside-chamber residual in the `IJ` orientation. -/
def eIJ (G : ℝ) (n p q s : ℕ) : ℝ := covarianceTail G n p q 1 s

/-- Literal outside-chamber residual in the `JJ` orientation. -/
def eJJ (G : ℝ) (n p q r s : ℕ) : ℝ := covarianceTail G n p q r s

/-- Literal outside-chamber residual in the diagonal orientation. -/
def eD (G : ℝ) (n p r : ℕ) : ℝ := probabilityTail G n p r













end

end Erdos390.Full.PaperPrimePowerFourDisplays

end

/- Source module: Erdos390.Full.PaperPrimePowerTailRow -/
section


/-!
# The literal beyond-four residual row

The residual functions of the four pointwise displays are exactly supported
on the finite beyond-four exponent sets.  This file identifies those sums
and applies the previously proved actual-cutoff tail ledgers.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerTailRow

open ArithmeticModel Scale ValuationCutoff
open OmittedTiltPairChamber
open PaperPrimePowerTailLedger PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays
open PrimeSums

noncomputable section

















/-! ## One row majorant -/

/-- Explicit common majorant for all four outside-chamber residual rows. -/
def tailRowMajorant (G : ℝ) (W n : ℕ) : ℝ :=
  let T := G + G ^ 2
  let K := cutoffScale W * L n
  let Y := (yNat n : ℝ)
  T * ((K / Y) * (bandReciprocalSum n W + 1)) +
    T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) +
      6 * G * (K ^ 2 / Y ^ 2)







/-! ## Vanishing of the row majorant -/



/-- A convenient real-power upper bound for `tailRowMajorant`. -/
def tailRowLimitMajorant (G : ℝ) (W n : ℕ) : ℝ :=
  let T := G + G ^ 2
  let c := cutoffScale W
  (13 * T * c) * (L n ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ)) +
    (T * c ^ 2) * (L n ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ)) +
      (6 * G * c ^ 2) * (L n ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ))











end

end Erdos390.Full.PaperPrimePowerTailRow

end

/- Source module: Erdos390.Full.PaperPrimePowerRemainderRate -/
section


/-!
# Common vanishing remainder for Lemma 7.5

The omitted-score error must survive one complete harmonic prime sum.  This
file propagates the strengthened `epsilon * log L -> 0` estimate through the
local restoration and covariance polynomials, and then combines it with the
literal beyond-four row.
-/

open Filter Topology

namespace Erdos390.Full.PaperPrimePowerRemainderRate

open ArithmeticModel Scale PrimeSums
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerPairAggregation PaperPrimePowerTailRow

noncomputable section













/-- The exact remainder appearing after finite aggregation. -/
def primePowerRowRemainder
    (epsilon : ℕ → ℝ) (G₀ B Gf : ℝ) (W n : ℕ) : ℝ :=
  pairAggregationConstant *
      primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n) *
      (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) +
    tailRowMajorant Gf W n





end

end Erdos390.Full.PaperPrimePowerRemainderRate

end

/- Source module: Erdos390.Full.PaperPrimePowerLemma75 -/
section


/-!
# Exact export of paper Lemma 7.5

This module joins the literal four-mark chamber, the arbitrary-power
fallback, the four prime-power orientations, and their finite row
aggregation.  The final constant is independent of the tilt box.  All box
dependence is confined to a single remainder tending to zero.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerLemma75

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open DickmanFourMarkProductKernel
open FullTiltPairChamber FullTiltPairHarmonicRate
open FullTiltPrimePowerFallback
open OmittedTiltPairChamber PaperScaleMarkedCell LocalFugacityBounds
open PaperTwoLocalRestorationBound PaperValuationCutoff
open PaperPrimePowerChamberError PaperPrimePowerActualSplice
open PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerSumAbsAggregation
open ValuationCutoff PrimeSums PaperPrimePowerRow

noncomputable section

/-- The main row constant.  Its only non-universal input is the
box-independent Dickman four-mark kernel constant. -/
def paperPrimePowerConstant (C_K : ℝ) : ℝ :=
  pairAggregationConstant * primePowerMainConstant C_K *
    (2 * Real.log 4 + 5)







/-- The five simultaneous conclusions of paper Lemma 7.5.  In particular,
the first three fields are sums of absolute pointwise covariances, not the
weaker absolute value of an already summed covariance. -/
structure PrimePowerTransferBounds
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (n W : ℕ)
    (C_pow epsilon_BW : ℝ) : Prop where
  ji : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
    (∑ r ∈ highExponents (valuationCutoff p M),
      |law.probability.covariance (law.Ip p r) (law.I q)|) ≤
        (C_pow * tPrime n p * tPrime n q + epsilon_BW) *
          (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ))
  ij : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
    (∑ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.I p) (law.Ip q s)|) ≤
        (C_pow * tPrime n p * tPrime n q + epsilon_BW) *
          (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2
  jj : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
    (∑ r ∈ highExponents (valuationCutoff p M),
      ∑ s ∈ highExponents (valuationCutoff q M),
        |law.probability.covariance (law.Ip p r) (law.Ip q s)|) ≤
      (C_pow * tPrime n p * tPrime n q + epsilon_BW) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2
  diagonal : ∀ p ∈ primeBand n W,
    law.probability.expect (fun omega ↦ law.J p omega ^ 2) ≤
      (C_pow + epsilon_BW) * (1 / (p : ℝ)) ^ 2
  row : ∀ p ∈ primeBand n W,
    (p : ℝ) * ∑ q ∈ primeBand n W,
      |law.covVV p q - law.covII p q| ≤
        C_pow * (1 / (W : ℝ)) + epsilon_BW







end

end Erdos390.Full.PaperPrimePowerLemma75

end

/- Source module: Erdos390.Full.PaperPrimePowerGenericAggregation -/
section


/-!
# Generic finite aggregation for the five conclusions of Lemma 7.5

This module separates the finite prime-power summation from the source of
the pointwise estimates.  It can therefore be applied both to one
structured cell and to a tagged fixed finite mixture.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerGenericAggregation

open ArithmeticModel Scale
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerChamberError PaperPrimePowerPairAggregation
open PaperPrimePowerSumAbsAggregation PaperPrimePowerRow
open PaperPrimePowerLemma75 PaperValuationCutoff
open ValuationCutoff PrimeSums LocalFugacityBounds

noncomputable section

/-- A single nonnegative error large enough for all three product-weighted
sums, the diagonal square, and the row estimate. -/
def genericAggregationRemainder
    (E Tlin Tquad Tdiag Trow : ℝ) (n W : ℕ) : ℝ :=
  pairAggregationConstant * E + Tlin + Tquad + Tdiag +
    pairAggregationConstant * E *
      (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) + Trow





end

end Erdos390.Full.PaperPrimePowerGenericAggregation

end

/- Source module: Erdos390.Full.FixedFiniteMixtureFullUniform -/
section


/-!
# Full uniform Lemma 7.5 for a fixed finite family of actual cells

This file specializes the marked-cell and full-tilt asymptotics on every
member of a fixed finite family, takes finite common majorants, and applies
the exact tagged-mixture theorem.  No desired covariance or tail estimate
is assumed by the final export.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.FixedFiniteMixtureFullUniform

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPairHarmonicRate FullTiltPrimePowerFallback
open DickmanFourMarkProductKernel PaperScaleMarkedCell
open PaperTwoLocalRestorationBound LocalFugacityBounds
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerLemma75 PaperPrimePowerGenericAggregation
open FixedFiniteMixtureLemma75 PaperValuationCutoff ValuationCutoff
open PrimeSums

noncomputable section

/-- Monotonicity of the integral physical endpoint. -/
theorem physicalBound_mono {C D : ℝ} (hCD : C ≤ D) (n : ℕ) :
    physicalBound C n ≤ physicalBound D n := by
  unfold physicalBound
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right hCD (by positivity)

@[simp] theorem coefficientScale_zero (W n : ℕ) :
    coefficientScale 0 W n = 0 := by
  unfold coefficientScale
  ring



@[simp] theorem pairProbabilityScale_half_zero (x : ℝ) :
    pairProbabilityScale (x / 2) 0 0 = x := by
  unfold pairProbabilityScale localRestorationScale
  ring

variable {Cell : Type*} [Fintype Cell]

/-- The single prime-power constant used for every finite head family and
every later tilt box.  Its definition contains only the fixed Dickman
four-mark kernel witness. -/
noncomputable def boxIndependentPrimePowerConstant : ℝ :=
  paperPrimePowerConstant boxIndependentFourMarkKernelConstant





end

end Erdos390.Full.FixedFiniteMixtureFullUniform

end

/- Source module: Erdos390.Full.PaperCanonicalNuisanceEffectiveGap -/
section


/-!
# Canonical finite nuisance gap on a preselected effective box

This file keeps the baseline covariance at the actual finite `n`.  It first
uses the positive barycentric cell masses and the two separated physical
pools to obtain a literal baseline nuisance gap, and then transfers that gap
to a bounded effective tilt by the exact finite density-ratio inequality.
No limiting mixture is selected or assumed to exist.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The quadratic form of the literal nuisance operator is the scalar
variance of the corresponding nuisance linear statistic under the actual
finite tilted law. -/
theorem tiltedLaw_covariance_nuisanceStatistic [Nonempty Head]
    (xi : B.ParamSpace) (z : B.NuisanceSpace) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m))
        (fun m ↦ inner ℝ z (B.nuisanceStatistic m)) =
      inner ℝ z (B.nuisanceCovarianceOperator xi z) := by
  rw [B.nuisanceCovarianceOperator_quadratic]
  rfl

/-- The explicit nuisance gap used on an effective box of radius `a`. -/
def canonicalEffectiveNuisanceGamma [Nonempty Head]
    (I : PhysicalIntervals) (U a : ℝ)
    (T : BarycentricTarget B.sampleData) : ℝ :=
  Real.exp (-2 *
      ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
        B.nuisanceStatisticCoefficient U) * a)) *
    B.uniformNuisanceGap T.cellMassMargin
      (Real.log (I.lower .plus) - Real.log (I.upper .minus))
      (Real.log U)

theorem canonicalEffectiveNuisanceGamma_pos [Nonempty Head]
    (I : PhysicalIntervals) (U a : ℝ)
    (T : BarycentricTarget B.sampleData) :
    0 < B.canonicalEffectiveNuisanceGamma I U a T := by
  unfold canonicalEffectiveNuisanceGamma
  exact mul_pos (Real.exp_pos _)
    (B.uniformNuisanceGap_pos T.cellMassMargin_pos
      (fixedInterval_separation_pos I))

/-- Uniform nuisance gap on a preselected effective box, specialized to the
actual canonical barycentric baseline.  The gap is finite-`n` and explicit;
its positive density-ratio factor may depend on the already selected box
radius `a`, but there is no convergence hypothesis on the baseline weights.
-/
theorem nuisanceCovarianceOperator_effectiveBox_canonicalBaseline
    [Nonempty Head]
    (I : PhysicalIntervals) {U a : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (T : BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (xi : B.ParamSpace) (hxi : B.paperEffectiveSize xi ≤ a)
    (z : B.NuisanceSpace) :
    (Real.exp (-2 *
          ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
            B.nuisanceStatisticCoefficient U) * a)) *
        B.uniformNuisanceGap T.cellMassMargin
          (Real.log (I.lower .plus) - Real.log (I.upper .minus))
          (Real.log U)) * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z) := by
  let gamma : ℝ := B.uniformNuisanceGap T.cellMassMargin
    (Real.log (I.lower .plus) - Real.log (I.upper .minus))
    (Real.log U)
  let K : ℝ :=
    (PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
      B.nuisanceStatisticCoefficient U) * a
  let F : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ z (B.nuisanceStatistic m)
  have hweight : ∀ c : Cell Head,
      T.cellMassMargin ≤ B.baseline.normalizedCellMass c := by
    intro c
    rw [hbaseline]
    exact T.cellMassMargin_le c
  have hbaseOperator : gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator 0 z) := by
    exact B.nuisanceCovarianceOperator_zero_fixedIntervals I
      T.cellMassMargin_pos hlowerOne hupperU hlo hhi hweight z
  have hbase : gamma * ‖z‖ ^ 2 ≤
      B.baselineSigmaProbability.covariance F F := by
    rw [B.baselineSigmaProbability_eq_tiltedLaw_zero]
    dsimp only [F]
    rw [B.tiltedLaw_covariance_nuisanceStatistic 0 z]
    exact hbaseOperator
  have hscore : ∀ m : B.sampleData.Sample,
      |B.scaledBridgeScore xi m| ≤ K := by
    intro m
    exact B.effectiveScoreBound_of_paperEffectiveSize
      hU hW (fun sigma ↦ (hhi sigma).trans_le
        (FixedFiniteMixtureFullUniform.physicalBound_mono
          (hupperU sigma) B.sampleData.n)) xi hxi m
  have hdom :=
    B.baselineSigmaProbability.exp_neg_two_mul_covariance_self_le_exponentialTilt
      F (B.scaledBridgeScore xi) K hscore
  have hfactor : 0 ≤ Real.exp (-2 * K) := (Real.exp_pos _).le
  have hchain : Real.exp (-2 * K) * (gamma * ‖z‖ ^ 2) ≤
      ((B.baselineSigmaProbability).exponentialTilt
        (B.scaledBridgeScore xi)).covariance F F :=
    (mul_le_mul_of_nonneg_left hbase hfactor).trans hdom
  rw [← B.tiltedLaw_eq_exponentialTilt_baseline] at hchain
  rw [B.tiltedLaw_covariance_nuisanceStatistic xi z] at hchain
  simpa only [gamma, K, mul_assoc] using hchain

/-- Named-gap form of
`nuisanceCovarianceOperator_effectiveBox_canonicalBaseline`, convenient for
the exact Schur regression constructors. -/
theorem canonicalEffectiveNuisanceGapProof
    [Nonempty Head]
    (I : PhysicalIntervals) {U a : ℝ}
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (T : BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (xi : B.ParamSpace) (hxi : B.paperEffectiveSize xi ≤ a) :
    ∀ z : B.NuisanceSpace,
      B.canonicalEffectiveNuisanceGamma I U a T * ‖z‖ ^ 2 ≤
        inner ℝ z (B.nuisanceCovarianceOperator xi z) := by
  intro z
  simpa only [canonicalEffectiveNuisanceGamma, mul_assoc] using
    B.nuisanceCovarianceOperator_effectiveBox_canonicalBaseline I hU
      hlowerOne hupperU hlo hhi T hbaseline hW xi hxi z

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalNuisanceEffectiveBall -/
section


/-!
# Canonical nuisance gap on the actual effective ODE ball

The canonical finite nuisance theorem is stated in the paper effective
size.  The ODE is run in the equivalent effective max norm.  This file
records the exact conversion, including the factor three, so later Schur
constructors need not assume a nuisance gap separately.
-/

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The root canonical finite nuisance gap, specialized to every point of
the preselected effective ODE ball. -/
theorem canonicalEffectiveNuisanceGap_on_closedBall
    [Nonempty Head]
    (I : PhysicalIntervals) {U : ℝ} (a : NNReal)
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (T : BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline)
    (hW : 1 < B.sampleData.W)
    (z : B.EffectiveParamSpace)
    (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) :
    ∀ v : B.NuisanceSpace,
      B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T *
          ‖v‖ ^ 2 ≤
        inner ℝ v
          (B.nuisanceCovarianceOperator (B.effectiveParamEquiv z) v) := by
  have hznorm : ‖z‖ ≤ (a : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hsize : B.paperEffectiveSize (B.effectiveParamEquiv z) ≤
      3 * (a : ℝ) :=
    (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hznorm (by norm_num))
  exact B.canonicalEffectiveNuisanceGapProof I hU hlowerOne hupperU
    hlo hhi T hbaseline hW (B.effectiveParamEquiv z) hsize

end BridgeData

end


end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperPrimePowerRelativeQuadratic -/
section


/-!
# Relative prime-power quadratic transfer for Lemma 8.6

Lemma 7.5 supplies a genuine weighted row estimate for the difference
between full valuation covariance and squarefree covariance.  This file
proves, by finite summation, that the row estimate gives an error at the
relative `w^2` scale for the actual compensated coefficient vector.  The
proof does not replace `sum |Cov|` by `|sum Cov|`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerRelativeQuadratic

open ArithmeticModel PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75

noncomputable section

variable {Omega : Type*} [Fintype Omega] {M : ℕ}

/-- Full-valuation covariance quadratic form on a finite prime set. -/
def fullValuationQuadratic
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, ∑ q ∈ S, c p * c q * law.covVV p q

/-- Squarefree covariance quadratic form on the same finite prime set. -/
def squarefreeQuadratic
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, ∑ q ∈ S, c p * c q * law.covII p q











/-- The full-valuation marked covariance row paired with a coefficient
vector. -/
def fullMarkedRow
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) (p : ℕ) : ℝ :=
  law.probability.covariance (law.V p)
    (fun omega ↦ ∑ q ∈ S, c q * law.V q omega)

/-- Squarefree companion to `fullMarkedRow`. -/
def squarefreeMarkedRow
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) (p : ℕ) : ℝ :=
  law.probability.covariance (law.I p)
    (fun omega ↦ ∑ q ∈ S, c q * law.I q omega)







end

end Erdos390.Full.PaperPrimePowerRelativeQuadratic

end


