-- Prove2me | solution 1 for Erdos390.Full.DickmanBasic.kernel_secondDerivative_first_bound
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T13:44:38.229792+00:00
-- url     : https://prove2.me/submissions/cc3625c3-fddb-4fec-bba8-d57b8fe7d5ff

import Definitions.Def_erdos390_dickman_step_function
import Mathlib

/-!
# The Dickman function on the finite range needed for Erdős 390

This file constructs the Dickman function by the method of steps.  No
existence, regularity, positivity, or kernel estimate is assumed as an input.
Only the range up to `5` is needed for the Poisson--Dickman operator at
`U = 9 / 2`.
-/

open Filter Set
open scoped Interval

noncomputable section

namespace Erdos390.Full.DickmanBasic



lemma safeDenom_pos (x : ℝ) : 0 < safeDenom x := by
  unfold safeDenom
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

lemma safeDenom_ne_zero (x : ℝ) : safeDenom x ≠ 0 :=
  ne_of_gt (safeDenom_pos x)

lemma safeDenom_eq_self {x : ℝ} (hx : 1 ≤ x) : safeDenom x = x := by
  simp [safeDenom, hx]







lemma rhoApprox_succ_of_one_lt (n : ℕ) {x : ℝ} (hx : 1 < x) :
    rhoApprox (n + 1) x =
      1 - ∫ t in (1 : ℝ)..x, rhoApprox n (t - 1) / safeDenom t := by
  simp [rhoApprox, not_le.mpr hx]

lemma continuous_safeDenom : Continuous safeDenom := by
  exact continuous_id.max continuous_const

lemma continuous_stepIntegrand (n : ℕ) :
    Continuous (fun t : ℝ => rhoApprox n (t - 1) / safeDenom t) := by
  induction n with
  | zero =>
      exact continuous_const.div continuous_safeDenom safeDenom_ne_zero
  | succ n ih =>
      have hRho : Continuous (rhoApprox (n + 1)) := by
        let g : ℝ → ℝ := fun t => rhoApprox n (t - 1) / safeDenom t
        have hg : Continuous g := by
          simpa [g] using ih
        have hprimitive : Continuous (fun x : ℝ => ∫ t in (1 : ℝ)..x, g t) :=
          (intervalIntegral.differentiable_integral_of_continuous hg).continuous
        have hbranch : Continuous (fun x : ℝ => 1 - ∫ t in (1 : ℝ)..x, g t) :=
          continuous_const.sub hprimitive
        have hpiece : Continuous (fun x : ℝ =>
            if x ≤ 1 then (1 : ℝ)
            else 1 - ∫ t in (1 : ℝ)..x, g t) := by
          apply continuous_if_le continuous_id continuous_const
            continuous_const.continuousOn hbranch.continuousOn
          intro x hx
          change x = 1 at hx
          rw [hx]
          simp
        simpa [rhoApprox, g] using hpiece
      exact (hRho.comp (continuous_id.sub continuous_const)).div
        continuous_safeDenom safeDenom_ne_zero

lemma continuous_rhoApprox (n : ℕ) : Continuous (rhoApprox n) := by
  cases n with
  | zero => exact continuous_const
  | succ n =>
      let g : ℝ → ℝ := fun t => rhoApprox n (t - 1) / safeDenom t
      have hg : Continuous g := continuous_stepIntegrand n
      have hprimitive : Continuous (fun x : ℝ => ∫ t in (1 : ℝ)..x, g t) :=
        (intervalIntegral.differentiable_integral_of_continuous hg).continuous
      have hbranch : Continuous (fun x : ℝ => 1 - ∫ t in (1 : ℝ)..x, g t) :=
        continuous_const.sub hprimitive
      have hpiece : Continuous (fun x : ℝ =>
          if x ≤ 1 then (1 : ℝ)
          else 1 - ∫ t in (1 : ℝ)..x, g t) := by
        apply continuous_if_le continuous_id continuous_const
          continuous_const.continuousOn hbranch.continuousOn
        intro x hx
        change x = 1 at hx
        rw [hx]
        simp
      simpa [rhoApprox, g] using hpiece

/-- Successive method-of-steps approximants agree on the interval which
has already been constructed. -/
lemma rhoApprox_succ_eq_prev : ∀ (n : ℕ) (x : ℝ),
    x ≤ (n : ℝ) + 1 → rhoApprox (n + 1) x = rhoApprox n x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx1 : x ≤ 1 := by simpa using hx
      simp [rhoApprox, hx1]
  | succ n ih =>
      intro x hx
      by_cases hx1 : x ≤ 1
      · simp [rhoApprox, hx1]
      · have h1x : 1 < x := lt_of_not_ge hx1
        rw [rhoApprox_succ_of_one_lt (n + 1) h1x,
          rhoApprox_succ_of_one_lt n h1x]
        congr 1
        apply intervalIntegral.integral_congr
        intro t ht
        have htmem : t ∈ Icc (1 : ℝ) x := by
          simpa [uIcc_of_le h1x.le] using ht
        have htbound : t - 1 ≤ (n : ℝ) + 1 := by
          have hcast : x ≤ (n : ℝ) + 2 := by
            norm_num [Nat.cast_add, Nat.cast_one, add_assoc] at hx ⊢
            exact hx
          linarith [htmem.2]
        change rhoApprox (n + 1) (t - 1) / safeDenom t =
          rhoApprox n (t - 1) / safeDenom t
        rw [ih (t - 1) htbound]

lemma hasDerivAt_rhoApprox_succ (n : ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (rhoApprox (n + 1))
      (-rhoApprox n (x - 1) / x) x := by
  let g : ℝ → ℝ := fun t => rhoApprox n (t - 1) / safeDenom t
  have hg : Continuous g := by
    simpa [g] using continuous_stepIntegrand n
  have hprimitive : HasDerivAt (fun z : ℝ => ∫ t in (1 : ℝ)..z, g t) (g x) x :=
    (hg.integral_hasStrictDerivAt 1 x).hasDerivAt
  have hbranch : HasDerivAt
      (fun z : ℝ => 1 - ∫ t in (1 : ℝ)..z, g t) (-g x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub hprimitive using 1
    ring
  have heq : rhoApprox (n + 1) =ᶠ[nhds x]
      (fun z : ℝ => 1 - ∫ t in (1 : ℝ)..z, g t) := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    simpa [g] using rhoApprox_succ_of_one_lt n hz
  have h := hbranch.congr_of_eventuallyEq heq
  have hgx : g x = rhoApprox n (x - 1) / x := by
    simp [g, safeDenom_eq_self hx.le]
  rw [hgx] at h
  convert h using 1
  ring



lemma continuous_rho : Continuous rho := by
  exact continuous_rhoApprox 5

lemma rho_eq_one_of_le_one {x : ℝ} (hx : x ≤ 1) : rho x = 1 := by
  simp [rho, rhoApprox, hx]



@[simp] lemma rho_one : rho 1 = 1 := rho_eq_one_of_le_one le_rfl

/-- The delay differential equation on the entire range needed later. -/
lemma hasDerivAt_rho {x : ℝ} (hx1 : 1 < x) (hx6 : x ≤ 6) :
    HasDerivAt rho (-rho (x - 1) / x) x := by
  have hprev : rhoApprox 5 (x - 1) = rhoApprox 4 (x - 1) := by
    apply rhoApprox_succ_eq_prev 4
    norm_num
    linarith
  have h := hasDerivAt_rhoApprox_succ 4 hx1
  simpa [rho, hprev] using h

lemma deriv_rho {x : ℝ} (hx1 : 1 < x) (hx6 : x ≤ 6) :
    deriv rho x = -rho (x - 1) / x :=
  (hasDerivAt_rho hx1 hx6).deriv





/-- The integral of `rho` over its initial unit interval. -/
lemma integral_rho_zero_one :
    (∫ t in (0 : ℝ)..1, rho t) = 1 := by
  calc
    (∫ t in (0 : ℝ)..1, rho t) = ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      apply rho_eq_one_of_le_one
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le zero_le_one] using ht
      exact ht'.2
    _ = 1 := by simp

/-- The delay equation has the equivalent positive averaging form
`x * rho x = ∫_[x-1,x] rho`.  This identity is the key to positivity. -/
lemma rho_average_eq {x : ℝ} (hx1 : 1 ≤ x) (hx5 : x ≤ 5) :
    x * rho x = ∫ t in (x - 1)..x, rho t := by
  rcases hx1.eq_or_lt with rfl | hx1
  · simp [rho_one, integral_rho_zero_one]
  · have hderiv : ∀ t ∈ Ioo (1 : ℝ) x,
        HasDerivWithinAt (fun u : ℝ => u * rho u)
          (rho t - rho (t - 1)) (Ioi t) t := by
      intro t ht
      have ht6 : t ≤ 6 := by linarith [ht.2, hx5]
      have h := (hasDerivAt_id t).mul (hasDerivAt_rho ht.1 ht6)
      have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht.1)
      have heq : 1 * rho t + t * (-rho (t - 1) / t) =
          rho t - rho (t - 1) := by
        field_simp
        ring
      exact (h.congr_deriv heq).hasDerivWithinAt
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      hx1.le
      ((continuous_id.mul continuous_rho).continuousOn)
      hderiv
      ((continuous_rho.sub
        (continuous_rho.comp (continuous_id.sub continuous_const))).intervalIntegrable 1 x)
    have hshift : (∫ t in (1 : ℝ)..x, rho (t - 1)) =
        ∫ t in (0 : ℝ)..(x - 1), rho t := by
      convert intervalIntegral.integral_comp_sub_right
        (a := (1 : ℝ)) (b := x) rho 1 using 1
      norm_num
    have hsub : (∫ t in (1 : ℝ)..x, rho t - rho (t - 1)) =
        (∫ t in (1 : ℝ)..x, rho t) - ∫ t in (1 : ℝ)..x, rho (t - 1) := by
      apply intervalIntegral.integral_sub
      · exact continuous_rho.intervalIntegrable 1 x
      · exact (continuous_rho.comp
          (continuous_id.sub continuous_const)).intervalIntegrable 1 x
    have hadd₁ := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (continuous_rho.intervalIntegrable (0 : ℝ) 1)
      (continuous_rho.intervalIntegrable (1 : ℝ) x)
    have hadd₂ := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (continuous_rho.intervalIntegrable (0 : ℝ) (x - 1))
      (continuous_rho.intervalIntegrable (x - 1) x)
    rw [hsub, hshift] at hFTC
    rw [integral_rho_zero_one] at hadd₁
    have hrho1 : rho (1 : ℝ) = 1 := rho_one
    change _ = x * rho x - 1 * rho 1 at hFTC
    rw [hrho1] at hFTC
    norm_num at hFTC
    linarith

/-- Positivity propagates across one unit interval.  The proof uses the
averaging identity, rather than any pre-existing fact about the classical
Dickman function. -/
private lemma rho_pos_step {a : ℝ} (ha1 : 1 ≤ a) (ha4 : a ≤ 4)
    (hprev : ∀ x ∈ Icc (a - 1) a, 0 < rho x) :
    ∀ x ∈ Icc a (a + 1), 0 < rho x := by
  have hanti : AntitoneOn rho (Icc a (a + 1)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a (a + 1)) continuous_rho.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_rho (by linarith [hx.1, ha1])
        (by linarith [hx.2, ha4])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hshift : x - 1 ∈ Icc (a - 1) a := by
        constructor <;> linarith [hx.1, hx.2]
      have hpos := hprev (x - 1) hshift
      rw [deriv_rho (by linarith [hx.1, ha1]) (by linarith [hx.2, ha4])]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpos.le)
        (by linarith [hx.1, ha1])
  have hend_le (x : ℝ) (hx : x ∈ Icc a (a + 1)) : rho (a + 1) ≤ rho x :=
    hanti hx (right_mem_Icc.mpr (by linarith)) hx.2
  have hIntegralLower : rho (a + 1) ≤ ∫ t in a..(a + 1), rho t := by
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (show a ≤ a + 1 by linarith)
      (continuous_const.intervalIntegrable a (a + 1))
      (continuous_rho.intervalIntegrable a (a + 1))
      (fun x hx => hend_le x hx)
    simpa using hmono
  have hAverage : (a + 1) * rho (a + 1) = ∫ t in a..(a + 1), rho t := by
    have h := rho_average_eq (x := a + 1) (by linarith) (by linarith)
    rw [show a + 1 - 1 = a by ring] at h
    exact h
  have hend_nonneg : 0 ≤ rho (a + 1) := by
    nlinarith
  have hnonneg (x : ℝ) (hx : x ∈ Icc a (a + 1)) : 0 ≤ rho x :=
    hend_nonneg.trans (hend_le x hx)
  have hIntegralPos : 0 < ∫ t in a..(a + 1), rho t := by
    apply intervalIntegral.integral_pos (by linarith) continuous_rho.continuousOn
    · intro x hx
      exact hnonneg x ⟨hx.1.le, hx.2⟩
    · refine ⟨a, left_mem_Icc.mpr (by linarith), ?_⟩
      exact hprev a ⟨by linarith, le_rfl⟩
  have hend_pos : 0 < rho (a + 1) := by
    nlinarith
  intro x hx
  exact hend_pos.trans_le (hend_le x hx)

/-- Positivity of the finite method-of-steps solution on the full range used
in this file. -/
lemma rho_pos_on_zero_five {x : ℝ} (hx0 : 0 ≤ x) (hx5 : x ≤ 5) :
    0 < rho x := by
  have hzero_one : ∀ z ∈ Icc (0 : ℝ) 1, 0 < rho z := by
    intro z hz
    rw [rho_eq_one_of_le_one hz.2]
    norm_num
  have hone_two : ∀ z ∈ Icc (1 : ℝ) 2, 0 < rho z := by
    have hprev : ∀ z ∈ Icc ((1 : ℝ) - 1) 1, 0 < rho z := by
      intro z hz
      apply hzero_one z
      norm_num at hz ⊢
      exact hz
    have hstep := rho_pos_step (a := (1 : ℝ)) (by norm_num) (by norm_num) hprev
    intro z hz
    apply hstep z
    norm_num at hz ⊢
    exact hz
  have htwo_three : ∀ z ∈ Icc (2 : ℝ) 3, 0 < rho z := by
    have hprev : ∀ z ∈ Icc ((2 : ℝ) - 1) 2, 0 < rho z := by
      intro z hz
      apply hone_two z
      norm_num at hz ⊢
      exact hz
    have hstep := rho_pos_step (a := (2 : ℝ)) (by norm_num) (by norm_num) hprev
    intro z hz
    apply hstep z
    norm_num at hz ⊢
    exact hz
  have hthree_four : ∀ z ∈ Icc (3 : ℝ) 4, 0 < rho z := by
    have hprev : ∀ z ∈ Icc ((3 : ℝ) - 1) 3, 0 < rho z := by
      intro z hz
      apply htwo_three z
      norm_num at hz ⊢
      exact hz
    have hstep := rho_pos_step (a := (3 : ℝ)) (by norm_num) (by norm_num) hprev
    intro z hz
    apply hstep z
    norm_num at hz ⊢
    exact hz
  have hfour_five : ∀ z ∈ Icc (4 : ℝ) 5, 0 < rho z := by
    have hprev : ∀ z ∈ Icc ((4 : ℝ) - 1) 4, 0 < rho z := by
      intro z hz
      apply hthree_four z
      norm_num at hz ⊢
      exact hz
    have hstep := rho_pos_step (a := (4 : ℝ)) (by norm_num) (by norm_num) hprev
    intro z hz
    apply hstep z
    norm_num at hz ⊢
    exact hz
  by_cases hx1 : x ≤ 1
  · exact hzero_one x ⟨hx0, hx1⟩
  by_cases hx2 : x ≤ 2
  · exact hone_two x ⟨le_of_lt (lt_of_not_ge hx1), hx2⟩
  by_cases hx3 : x ≤ 3
  · exact htwo_three x ⟨le_of_lt (lt_of_not_ge hx2), hx3⟩
  by_cases hx4 : x ≤ 4
  · exact hthree_four x ⟨le_of_lt (lt_of_not_ge hx3), hx4⟩
  exact hfour_five x ⟨le_of_lt (lt_of_not_ge hx4), hx5⟩





private lemma continuousOn_delayDeriv :
    ContinuousOn delayDeriv (Ioo (1 : ℝ) 6) := by
  apply ContinuousOn.div
  · exact (continuous_rho.comp (continuous_id.sub continuous_const)).neg.continuousOn
  · exact continuous_id.continuousOn
  · intro x hx
    exact ne_of_gt (zero_lt_one.trans hx.1)

/-- The method-of-steps solution is continuously differentiable away from
the initial corner at `1`. -/
lemma contDiffOn_one_rho : ContDiffOn ℝ 1 rho (Ioo (1 : ℝ) 6) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (hasDerivAt_rho hx.1 hx.2.le).differentiableAt.differentiableWithinAt
  · intro h
    simp at h
  · rw [contDiffOn_zero]
    exact continuousOn_delayDeriv.congr fun x hx => by
      exact deriv_rho hx.1 hx.2.le

private lemma contDiffOn_one_delayDeriv :
    ContDiffOn ℝ 1 delayDeriv (Ioo (2 : ℝ) 5) := by
  have hshift : ContDiffOn ℝ 1 (fun x : ℝ => x - 1) (Ioo (2 : ℝ) 5) := by
    fun_prop
  have hmaps : MapsTo (fun x : ℝ => x - 1) (Ioo (2 : ℝ) 5) (Ioo (1 : ℝ) 6) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hcomp : ContDiffOn ℝ 1 (rho ∘ fun x : ℝ => x - 1) (Ioo (2 : ℝ) 5) :=
    contDiffOn_one_rho.comp hshift hmaps
  have hnum : ContDiffOn ℝ 1 (fun x : ℝ => -rho (x - 1)) (Ioo (2 : ℝ) 5) := by
    simpa [Function.comp_def] using hcomp.neg
  exact hnum.div contDiffOn_id fun x hx => ne_of_gt (by linarith [hx.1])

/-- On the compact interval needed for `U = 9/2`, the Dickman function is
`C²`.  We prove the slightly stronger open-interval statement first, so
ordinary derivatives can be used without endpoint conventions. -/
lemma contDiffOn_two_rho_open : ContDiffOn ℝ 2 rho (Ioo (2 : ℝ) 5) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨?_, ?_, ?_⟩
  · exact (contDiffOn_one_rho.mono fun x hx => by
      constructor <;> linarith [hx.1, hx.2]).differentiableOn (by norm_num)
  · intro h
    simp at h
  · exact contDiffOn_one_delayDeriv.congr fun x hx =>
      deriv_rho (by linarith [hx.1]) (by linarith [hx.2])





lemma rho_U_pos : 0 < rho U := by
  apply rho_pos_on_zero_five
  · norm_num [U]
  · norm_num [U]

lemma rho_U_ne_zero : rho U ≠ 0 := ne_of_gt rho_U_pos





@[simp] lemma F_zero : F 0 = 1 := by
  simp [F, rho_U_ne_zero]











/-- `F` is `C²` on an open neighborhood of `[0,2]`; retaining the open
neighborhood makes all later uses of ordinary derivatives unambiguous. -/
private lemma contDiffOn_two_F_open :
    ContDiffOn ℝ 2 F (Ioo (-(1 : ℝ) / 4) ((9 : ℝ) / 4)) := by
  have haff : ContDiffOn ℝ 2 (fun x : ℝ => U - x)
      (Ioo (-(1 : ℝ) / 4) ((9 : ℝ) / 4)) := by
    fun_prop
  have hmaps : MapsTo (fun x : ℝ => U - x)
      (Ioo (-(1 : ℝ) / 4) ((9 : ℝ) / 4)) (Ioo (2 : ℝ) 5) := by
    intro x hx
    norm_num [U] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hcomp : ContDiffOn ℝ 2 (rho ∘ fun x : ℝ => U - x)
      (Ioo (-(1 : ℝ) / 4) ((9 : ℝ) / 4)) :=
    contDiffOn_two_rho_open.comp haff hmaps
  simpa [F, Function.comp_def] using hcomp.div_const (rho U)



private lemma Icc_zero_two_subset_F_open :
    Icc (0 : ℝ) 2 ⊆ Ioo (-(1 : ℝ) / 4) ((9 : ℝ) / 4) := by
  intro x hx
  constructor <;> norm_num <;> linarith [hx.1, hx.2]

private lemma differentiableAt_F_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    DifferentiableAt ℝ F x := by
  have hxopen := Icc_zero_two_subset_F_open hx
  exact (contDiffOn_two_F_open.contDiffAt (isOpen_Ioo.mem_nhds hxopen)).differentiableAt
    (by norm_num)



private lemma contDiffOn_one_deriv_F_open :
    ContDiffOn ℝ 1 (deriv F) (Ioo (-(1 : ℝ) / 4) ((9 : ℝ) / 4)) := by
  exact contDiffOn_two_F_open.deriv_of_isOpen isOpen_Ioo (by norm_num)



private lemma differentiableAt_deriv_F_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    DifferentiableAt ℝ (deriv F) x := by
  have hxopen := Icc_zero_two_subset_F_open hx
  exact (contDiffOn_one_deriv_F_open.contDiffAt
    (isOpen_Ioo.mem_nhds hxopen)).differentiableAt (by norm_num)



/-- The derivative of the covariance kernel in its second coordinate also
vanishes linearly in the first coordinate.  This is the sharp input for
prime quadrature of `t * K(s,t)`: its Abel remainder is then proportional to
`s`, uniformly down to the moving low row. -/
lemma kernel_secondDerivative_first_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |deriv F (s + t) - F s * deriv F t| ≤ C * s := by
  have hFprimeCont : ContinuousOn (fun x : ℝ => ‖deriv F x‖)
      (Icc (0 : ℝ) 2) := by
    apply ContinuousOn.norm
    exact (contDiffOn_two_F_open.continuousOn_deriv_of_isOpen isOpen_Ioo
      (by norm_num)).mono Icc_zero_two_subset_F_open
  have hFsecondCont : ContinuousOn (fun x : ℝ => ‖deriv (deriv F) x‖)
      (Icc (0 : ℝ) 2) := by
    apply ContinuousOn.norm
    exact (contDiffOn_one_deriv_F_open.continuousOn_deriv_of_isOpen isOpen_Ioo
      (by norm_num)).mono Icc_zero_two_subset_F_open
  obtain ⟨x₁, hx₁, hmax₁⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (show (0 : ℝ) ≤ 2 by norm_num)) hFprimeCont
  obtain ⟨x₂, hx₂, hmax₂⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (show (0 : ℝ) ≤ 2 by norm_num)) hFsecondCont
  let M₁ : ℝ := ‖deriv F x₁‖
  let M₂ : ℝ := ‖deriv (deriv F) x₂‖
  have hM₁ : 0 ≤ M₁ := norm_nonneg _
  have hM₂ : 0 ≤ M₂ := norm_nonneg _
  have hbound₁ (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
      ‖deriv F x‖ ≤ M₁ := hmax₁ hx
  have hbound₂ (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
      ‖deriv (deriv F) x‖ ≤ M₂ := hmax₂ hx
  let C : ℝ := 1 + M₂ + M₁ * M₁
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro s hs t ht
  let G : ℝ → ℝ := fun x => deriv F (x + t) - F x * deriv F t
  have hGderiv (x : ℝ) (hx : x ∈ Icc (0 : ℝ) s) :
      HasDerivAt G
        (deriv (deriv F) (x + t) - deriv F x * deriv F t) x := by
    have hx₂ : x ∈ Icc (0 : ℝ) 2 := by
      constructor
      · exact hx.1
      · linarith [hx.2, hs.2]
    have hxt₂ : x + t ∈ Icc (0 : ℝ) 2 := by
      constructor <;> linarith [hx.1, hx.2, hs.2, ht.1, ht.2]
    have hshift : HasDerivAt (fun y : ℝ => y + t) 1 x :=
      (hasDerivAt_id x).add_const t
    have hfirst :=
      (differentiableAt_deriv_F_of_mem hxt₂).hasDerivAt.comp x hshift
    have hsecond :=
      (differentiableAt_F_of_mem hx₂).hasDerivAt.mul_const (deriv F t)
    simpa only [G, Function.comp_apply, mul_one, Pi.sub_apply]
      using hfirst.sub hsecond
  have hGbound (x : ℝ) (hx : x ∈ Icc (0 : ℝ) s) :
      ‖deriv G x‖ ≤ C := by
    have hx₂ : x ∈ Icc (0 : ℝ) 2 := by
      constructor
      · exact hx.1
      · linarith [hx.2, hs.2]
    have ht₂ : t ∈ Icc (0 : ℝ) 2 :=
      ⟨ht.1, ht.2.trans (by norm_num)⟩
    have hxt₂ : x + t ∈ Icc (0 : ℝ) 2 := by
      constructor <;> linarith [hx.1, hx.2, hs.2, ht.1, ht.2]
    rw [(hGderiv x hx).deriv]
    calc
      ‖deriv (deriv F) (x + t) - deriv F x * deriv F t‖ ≤
          ‖deriv (deriv F) (x + t)‖ +
            ‖deriv F x * deriv F t‖ := norm_sub_le _ _
      _ ≤ M₂ + M₁ * M₁ := by
        rw [norm_mul]
        exact add_le_add (hbound₂ (x + t) hxt₂)
          (mul_le_mul (hbound₁ x hx₂) (hbound₁ t ht₂)
            (norm_nonneg _) hM₁)
      _ ≤ C := by dsimp only [C]; linarith
  have hdiff : ‖G s - G 0‖ ≤ C * ‖s - 0‖ := by
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hGderiv x hx).differentiableAt) hGbound
      (convex_Icc (0 : ℝ) s) (left_mem_Icc.mpr hs.1)
      (right_mem_Icc.mpr hs.1)
  dsimp only [G] at hdiff
  rw [F_zero] at hdiff
  norm_num [Real.norm_eq_abs, abs_of_nonneg hs.1] at hdiff ⊢
  simpa only [zero_add, one_mul] using hdiff

end Erdos390.Full.DickmanBasic

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |deriv Erdos390.Full.DickmanBasic.F (s + t) -
        Erdos390.Full.DickmanBasic.F s * deriv Erdos390.Full.DickmanBasic.F t| ≤ C * s := by
  exact Erdos390.Full.DickmanBasic.kernel_secondDerivative_first_bound
