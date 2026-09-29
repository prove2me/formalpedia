-- Prove2me | solution 1 for BanditAlgorithm.pinsker_squared_event_difference
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-07-19T03:57:29.973775+00:00
-- url     : https://prove2.me/submissions/23fb960b-a26f-46ac-b25a-2efc1e3b28b1

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open MeasureTheory InformationTheory Real Set
open scoped ENNReal

/-!
Source: T. Lattimore and C. Szepesvari, *Bandit Algorithms* (CUP 2020),
Note 5, Eq. (14.12), printed p. 193 / PDF p. 202.

The proof applies Jensen's inequality to the Radon-Nikodym density separately
on an event and its complement.  The resulting binary relative entropy is at
least twice the squared probability gap: after subtracting that square, its
second derivative in the first Bernoulli parameter is
`1 / (p * (1 - p)) - 4`, which is nonnegative on `(0, 1)`.
-/

theorem solution {Omega : Type} {mOmega : MeasurableSpace Omega}
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Omega} (hA : MeasurableSet A) (hD : klDiv P Q ≠ ∞) :
    2 * (Q.real A - P.real A) ^ 2 ≤ (klDiv P Q).toReal := by
  have hPQ : P ≪ Q := (klDiv_ne_top_iff.mp hD).1
  have hllr : Integrable (llr P Q) P := (klDiv_ne_top_iff.mp hD).2
  have hint : Integrable (fun x => klFun (P.rnDeriv Q x).toReal) Q :=
    (integrable_klFun_rnDeriv_iff hPQ).2 hllr
  have hevent : ∀ {S : Set Omega}, MeasurableSet S →
      Q.real S * klFun (P.real S / Q.real S) ≤
        ∫ x in S, klFun (P.rnDeriv Q x).toReal ∂Q := by
    intro S hS
    have hPSQS : P.restrict S ≪ Q.restrict S := hPQ.restrict S
    have hQSQ : Q.restrict S ≪ Q := Measure.absolutelyContinuous_restrict
    have hrn : (P.restrict S).rnDeriv (Q.restrict S) =ᵐ[Q.restrict S]
        P.rnDeriv Q := by
      have hchain := Measure.rnDeriv_mul_rnDeriv (κ := Q) hPSQS
      have hq := Measure.rnDeriv_restrict_self Q hS
      have hp := Measure.rnDeriv_restrict P Q hS
      filter_upwards [hQSQ hchain, hQSQ hq, hQSQ hp, ae_restrict_mem hS]
        with x hchain_x hq_x hp_x hx
      simp only [Pi.mul_apply, Set.indicator_of_mem hx, Pi.one_apply] at hchain_x hq_x hp_x
      rw [hq_x, mul_one, hp_x] at hchain_x
      exact hchain_x
    have hfun := hrn.fun_comp (fun z : ENNReal => klFun z.toReal)
    have hintS : Integrable
        (fun x => klFun ((P.restrict S).rnDeriv (Q.restrict S) x).toReal)
        (Q.restrict S) := hint.integrableOn.congr hfun.symm
    have hj := mul_le_integral_rnDeriv_of_ac convexOn_klFun
      continuous_klFun.continuousWithinAt hintS hPSQS
    simpa only [measureReal_restrict_apply_univ] using
      hj.trans_eq (integral_congr_ae hfun)
  have hbinary_le :
      Q.real A * klFun (P.real A / Q.real A) +
          Q.real Aᶜ * klFun (P.real Aᶜ / Q.real Aᶜ) ≤
        (klDiv P Q).toReal := by
    calc
      Q.real A * klFun (P.real A / Q.real A) +
          Q.real Aᶜ * klFun (P.real Aᶜ / Q.real Aᶜ)
          ≤ (∫ x in A, klFun (P.rnDeriv Q x).toReal ∂Q) +
              ∫ x in Aᶜ, klFun (P.rnDeriv Q x).toReal ∂Q :=
        add_le_add (hevent hA) (hevent hA.compl)
      _ = ∫ x, klFun (P.rnDeriv Q x).toReal ∂Q :=
        integral_add_compl hA hint
      _ = (klDiv P Q).toReal := (toReal_klDiv_eq_integral_klFun hPQ).symm
  rw [probReal_compl_eq_one_sub hA, probReal_compl_eq_one_sub hA] at hbinary_le
  have hp : P.real A ∈ Set.Icc (0 : ℝ) 1 :=
    { left := measureReal_nonneg, right := measureReal_le_one }
  have hq : Q.real A ∈ Set.Icc (0 : ℝ) 1 :=
    { left := measureReal_nonneg, right := measureReal_le_one }
  by_cases hq0 : Q.real A = 0
  . have hQA : Q A = 0 := (measureReal_eq_zero_iff (μ := Q) (s := A)).mp hq0
    have hPA : P A = 0 := hPQ hQA
    have hp0 : P.real A = 0 :=
      (measureReal_eq_zero_iff (μ := P) (s := A)).mpr hPA
    simp [hq0, hp0]
  by_cases hq1 : Q.real A = 1
  . have hQAcReal : Q.real Aᶜ = 0 := by
      rw [probReal_compl_eq_one_sub hA, hq1]
      norm_num
    have hQAc : Q Aᶜ = 0 :=
      (measureReal_eq_zero_iff (μ := Q) (s := Aᶜ)).mp hQAcReal
    have hPAc : P Aᶜ = 0 := hPQ hQAc
    have hPAcReal : P.real Aᶜ = 0 :=
      (measureReal_eq_zero_iff (μ := P) (s := Aᶜ)).mpr hPAc
    have hp1 : P.real A = 1 := by
      rw [probReal_compl_eq_one_sub hA] at hPAcReal
      linarith
    simp [hq1, hp1]
  have hq_open : Q.real A ∈ Set.Ioo (0 : ℝ) 1 :=
    { left := lt_of_le_of_ne hq.1 (Ne.symm hq0),
      right := lt_of_le_of_ne hq.2 hq1 }
  have hbinary :
      2 * (Q.real A - P.real A) ^ 2 ≤
        Q.real A * klFun (P.real A / Q.real A) +
          (1 - Q.real A) * klFun ((1 - P.real A) / (1 - Q.real A)) := by
    let F : ℝ → ℝ := fun x =>
      -Real.binEntropy x - x * Real.log (Q.real A) -
        (1 - x) * Real.log (1 - Q.real A) - 2 * (Q.real A - x) ^ 2
    let F' : ℝ → ℝ := fun x =>
      Real.log x - Real.log (1 - x) - Real.log (Q.real A) +
        Real.log (1 - Q.real A) + 4 * (Q.real A - x)
    let F'' : ℝ → ℝ := fun x => x⁻¹ + (1 - x)⁻¹ - 4
    have hF : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) F := by
      refine convexOn_of_hasDerivWithinAt2_nonneg (f' := F') (f'' := F'')
        (convex_Icc 0 1) ?_ ?_ ?_ ?_
      . fun_prop
      . intro x hx
        rw [interior_Icc] at hx
        have hx0 : x ≠ 0 := ne_of_gt hx.1
        have hx1 : x ≠ 1 := ne_of_lt hx.2
        have hH := (Real.hasDerivAt_binEntropy hx0 hx1).neg
        have hxlog := (hasDerivAt_id x).mul_const (Real.log (Q.real A))
        have homx := (hasDerivAt_const x 1).sub (hasDerivAt_id x)
        have homxlog := homx.mul_const (Real.log (1 - Q.real A))
        have hquad :=
          (((hasDerivAt_const x (Q.real A)).sub (hasDerivAt_id x)).pow 2).const_mul 2
        convert (hH.sub hxlog |>.sub homxlog |>.sub hquad).hasDerivWithinAt using 1 <;>
          simp [F, F'] <;> ring
      . intro x hx
        rw [interior_Icc] at hx
        have hx0 : x ≠ 0 := ne_of_gt hx.1
        have hx1 : x ≠ 1 := ne_of_lt hx.2
        have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
        have hlogx := Real.hasDerivAt_log hx0
        have homx := (hasDerivAt_const x 1).sub (hasDerivAt_id x)
        have hlogomx := (Real.hasDerivAt_log hsub).comp x homx
        have hcq := hasDerivAt_const x (Real.log (Q.real A))
        have hcoq := hasDerivAt_const x (Real.log (1 - Q.real A))
        have hlin :=
          ((hasDerivAt_const x (Q.real A)).sub (hasDerivAt_id x)).const_mul 4
        convert (hlogx.sub hlogomx |>.sub hcq |>.add hcoq |>.add hlin).hasDerivWithinAt using 1 <;>
          simp [F', F''] <;> ring
      . intro x hx
        rw [interior_Icc] at hx
        have hxpos : 0 < x := hx.1
        have homxpos : 0 < 1 - x := sub_pos.mpr hx.2
        have hden : 0 < x * (1 - x) := mul_pos hxpos homxpos
        have hid : x⁻¹ + (1 - x)⁻¹ - 4 =
            (1 - 4 * (x * (1 - x))) / (x * (1 - x)) := by
          field_simp
          ring
        change 0 ≤ x⁻¹ + (1 - x)⁻¹ - 4
        rw [hid]
        exact div_nonneg (by nlinarith [sq_nonneg (2 * x - 1)]) hden.le
    have hqmem : Q.real A ∈ Set.Icc (0 : ℝ) 1 :=
      { left := hq_open.1.le, right := hq_open.2.le }
    have hqint : Q.real A ∈ interior (Set.Icc (0 : ℝ) 1) := by
      simpa [interior_Icc] using hq_open
    have hFqderiv : derivWithin F (Set.Ioi (Q.real A)) (Q.real A) = 0 := by
      have hH := (Real.hasDerivAt_binEntropy hq0 hq1).neg
      have hxlog := (hasDerivAt_id (Q.real A)).mul_const (Real.log (Q.real A))
      have homx :=
        (hasDerivAt_const (Q.real A) 1).sub (hasDerivAt_id (Q.real A))
      have homxlog := homx.mul_const (Real.log (1 - Q.real A))
      have hquad :=
        (((hasDerivAt_const (Q.real A) (Q.real A)).sub
          (hasDerivAt_id (Q.real A))).pow 2).const_mul 2
      have htotal := hH.sub hxlog |>.sub homxlog |>.sub hquad
      convert htotal.hasDerivWithinAt.derivWithin
        (uniqueDiffWithinAt_Ioi (Q.real A)) using 1 <;> simp [F] <;> ring
    have hmin := hF.isMinOn_of_rightDeriv_eq_zero hqint hFqderiv hp
    have hFq : F (Q.real A) = 0 := by
      simp only [F, Real.binEntropy]
      rw [Real.log_inv, Real.log_inv]
      ring
    have hFp : 0 ≤ F (P.real A) := by simpa [hFq] using hmin
    have homq : 1 - Q.real A ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
    by_cases hp0 : P.real A = 0
    . have hFp0 : 0 ≤ F 0 := by simpa [hp0] using hFp
      have hEq :
          Q.real A * klFun (0 / Q.real A) +
              (1 - Q.real A) * klFun ((1 - 0) / (1 - Q.real A)) -
                2 * (Q.real A - 0) ^ 2 = F 0 := by
        simp [F, klFun_apply]
        field_simp [homq]
        ring
      simpa [hp0] using (show 2 * (Q.real A - 0) ^ 2 ≤
          Q.real A * klFun (0 / Q.real A) +
            (1 - Q.real A) * klFun ((1 - 0) / (1 - Q.real A)) by
              nlinarith [hFp0, hEq])
    by_cases hp1 : P.real A = 1
    . have hFp1 : 0 ≤ F 1 := by simpa [hp1] using hFp
      have hEq :
          Q.real A * klFun (1 / Q.real A) +
              (1 - Q.real A) * klFun ((1 - 1) / (1 - Q.real A)) -
                2 * (Q.real A - 1) ^ 2 = F 1 := by
        simp [F, klFun_apply]
        field_simp [hq0]
        ring
      simpa [hp1] using (show 2 * (Q.real A - 1) ^ 2 ≤
          Q.real A * klFun (1 / Q.real A) +
            (1 - Q.real A) * klFun ((1 - 1) / (1 - Q.real A)) by
              nlinarith [hFp1, hEq])
    have homp : 1 - P.real A ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
    have hEq :
        Q.real A * klFun (P.real A / Q.real A) +
            (1 - Q.real A) * klFun ((1 - P.real A) / (1 - Q.real A)) -
              2 * (Q.real A - P.real A) ^ 2 = F (P.real A) := by
      rw [klFun_apply, klFun_apply, Real.log_div hp0 hq0,
        Real.log_div homp homq]
      simp only [F, Real.binEntropy, Real.log_inv]
      field_simp
      ring
    nlinarith
  exact hbinary.trans hbinary_le
