-- Prove2me | solution 1 for BanditAlgorithm.bandit_ucb_index_exponential_sum_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-28T15:50:59.673029+00:00
-- url     : https://prove2.me/submissions/f01f411d-e7f4-4a10-a723-a89faa57ee78

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim

open Filter MeasureTheory Real Set
open scoped BigOperators

namespace BanditAlgorithm

private lemma exponent_eq_shifted_sharp {t ε a : ℝ} (ht : 0 < t) (ha : 0 ≤ a) :
    -((t * (ε - Real.sqrt (2 * a / t))) ^ 2) / ((2 : ℝ) * t * 1) =
      -((ε * Real.sqrt t - Real.sqrt (2 * a)) ^ 2) / 2 := by
  rw [Real.sqrt_div (by positivity : 0 ≤ 2 * a) t]
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  field_simp
  nlinarith

private lemma summand_eq_shifted_sharp {t : ℕ} {ε a : ℝ}
    (ht : 1 ≤ t) (ha : 0 < a) :
    (if 2 * a / ε ^ 2 < (t : ℝ) then
        Real.exp (-((t : ℝ) * (ε - Real.sqrt (2 * a / t))) ^ 2 /
          ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
      else 1) =
    if 2 * a / ε ^ 2 < (t : ℝ) then
      Real.exp (-((ε * Real.sqrt t - Real.sqrt (2 * a)) ^ 2) / 2)
    else 1 := by
  split_ifs with hcut
  · congr 1
    apply exponent_eq_shifted_sharp
    · exact_mod_cast (show 0 < t from ht)
    · exact ha.le
  · rfl

private lemma shifted_sqrt_nonneg_sharp {t ε a : ℝ}
    (hε : 0 < ε) (ha : 0 < a)
    (ht : 2 * a / ε ^ 2 ≤ t) :
    0 ≤ ε * Real.sqrt t - Real.sqrt (2 * a) := by
  have hε0 : 0 ≤ ε := hε.le
  have ht0 : 0 ≤ t := by
    have hcut : 0 < 2 * a / ε ^ 2 := by positivity
    linarith
  have hsq : Real.sqrt (2 * a) ≤ Real.sqrt (ε ^ 2 * t) := by
    apply Real.sqrt_le_sqrt
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    rw [div_le_iff₀ hε2] at ht
    nlinarith
  rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε0] at hsq
  exact sub_nonneg.mpr hsq

private lemma shifted_gaussian_antitone_sharp {ε a : ℝ}
    (hε : 0 < ε) (ha : 0 < a) :
    AntitoneOn (fun t : ℝ ↦
      Real.exp (-((ε * Real.sqrt t - Real.sqrt (2 * a)) ^ 2) / 2))
      (Set.Ici (2 * a / ε ^ 2)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := by
    have hcut : 0 < 2 * a / ε ^ 2 := by positivity
    exact hcut.le.trans hx
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hsqrt : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hu : 0 ≤ ε * Real.sqrt x - Real.sqrt (2 * a) :=
    shifted_sqrt_nonneg_sharp hε ha hx
  have huv : ε * Real.sqrt x - Real.sqrt (2 * a) ≤
      ε * Real.sqrt y - Real.sqrt (2 * a) := by
    nlinarith
  have hsq : (ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2 ≤
      (ε * Real.sqrt y - Real.sqrt (2 * a)) ^ 2 := by
    nlinarith
  apply Real.exp_le_exp.mpr
  nlinarith

private lemma integral_x_mul_exp_neg_half_sq_sharp :
    ∫ x : ℝ in Set.Ioi 0, x * Real.exp (-(1 / 2 : ℝ) * x ^ 2) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (1 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.rpow_one] at h ⊢
  simpa only [Real.rpow_one] using h

private lemma integral_exp_neg_half_sq_sharp :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
      Real.sqrt (Real.pi / (1 / 2 : ℝ)) / 2 := by
  simpa using integral_gaussian_Ioi (1 / 2 : ℝ)

private lemma integral_shifted_gaussian_sharp (a : ℝ) :
    ∫ x : ℝ in Set.Ioi 0,
        (x + Real.sqrt (2 * a)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
      1 + Real.sqrt (2 * a) * (Real.sqrt (Real.pi / (1 / 2 : ℝ)) / 2) := by
  calc
    _ = (∫ x : ℝ in Set.Ioi 0, x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) +
        ∫ x : ℝ in Set.Ioi 0,
          Real.sqrt (2 * a) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
      rw [← integral_add]
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        ring
      · exact (integrable_mul_exp_neg_mul_sq
          (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
      · exact ((integrable_exp_neg_mul_sq
          (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _).integrableOn
    _ = _ := by
      rw [integral_x_mul_exp_neg_half_sq_sharp, integral_const_mul,
        integral_exp_neg_half_sq_sharp]

private lemma integral_shifted_gaussian_closed_sharp (a : ℝ) :
    ∫ x : ℝ in Set.Ioi 0,
        (x + Real.sqrt (2 * a)) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
      1 + Real.sqrt (Real.pi * a) := by
  rw [integral_shifted_gaussian_sharp]
  congr 1
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) a]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) Real.pi]
  rw [Real.sqrt_mul Real.pi_pos.le a]
  have hsqrt2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc
    Real.sqrt 2 * Real.sqrt a * (Real.sqrt 2 * Real.sqrt Real.pi / 2) =
        (Real.sqrt 2 ^ 2 / 2) * (Real.sqrt Real.pi * Real.sqrt a) := by ring
    _ = Real.sqrt Real.pi * Real.sqrt a := by rw [hsqrt2]; ring

private lemma gaussian_substitution_hasDerivAt_sharp {ε a s : ℝ}
    (hε : 0 < ε) :
    HasDerivAt (fun x : ℝ ↦ ((x + Real.sqrt (2 * a)) / ε) ^ 2)
      (2 * (s + Real.sqrt (2 * a)) / ε ^ 2) s := by
  convert (((hasDerivAt_id s).add_const (Real.sqrt (2 * a))).div_const ε).pow 2 using 1
  simp [id_eq]
  field_simp [ne_of_gt hε]

noncomputable def sharpUcbSummand (ε a x : ℝ) : ℝ :=
  if x ≤ 2 * a / ε ^ 2 then 1
  else Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2)

lemma sharpUcbSummand_nonneg (ε a x : ℝ) :
    0 ≤ sharpUcbSummand ε a x := by
  unfold sharpUcbSummand
  split <;> positivity

lemma sharpUcbSummand_antitone {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    AntitoneOn (sharpUcbSummand ε a) (Set.Ici 0) := by
  intro x hx y hy hxy
  change (if y ≤ 2 * a / ε ^ 2 then 1 else
      Real.exp (-((ε * Real.sqrt y - Real.sqrt (2 * a)) ^ 2) / 2)) ≤
    if x ≤ 2 * a / ε ^ 2 then 1 else
      Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2)
  by_cases hxc : x ≤ 2 * a / ε ^ 2
  · rw [if_pos hxc]
    by_cases hyc : y ≤ 2 * a / ε ^ 2
    · rw [if_pos hyc]
    · rw [if_neg hyc]
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg (ε * Real.sqrt y - Real.sqrt (2 * a))]
  · have hyc : ¬y ≤ 2 * a / ε ^ 2 := fun hyc ↦ hxc (hxy.trans hyc)
    rw [if_neg hxc, if_neg hyc]
    exact shifted_gaussian_antitone_sharp hε ha
      (le_of_lt (lt_of_not_ge hxc)) (le_of_lt (lt_of_not_ge hyc)) hxy

lemma sharpUcbSummand_nat_eq {t : ℕ} {ε a : ℝ}
    (ht : 1 ≤ t) (ha : 0 < a) :
    (if 2 * a / ε ^ 2 < (t : ℝ) then
        Real.exp (-((t : ℝ) *
          (ε - Real.sqrt (2 * a / t))) ^ 2 /
            ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
      else 1) =
      sharpUcbSummand ε a t := by
  rw [summand_eq_shifted_sharp (ε := ε) ht ha]
  unfold sharpUcbSummand
  by_cases h : 2 * a / ε ^ 2 < (t : ℝ)
  · rw [if_pos h, if_neg (not_le_of_gt h)]
  · rw [if_neg h, if_pos (le_of_not_gt h)]

lemma sharpUcbSummand_sum_le_intervalIntegral
    (n : ℕ) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    (∑ t ∈ Finset.Icc 1 n,
      if 2 * a / ε ^ 2 < (t : ℝ) then
        Real.exp (-((t : ℝ) *
          (ε - Real.sqrt (2 * a / t))) ^ 2 /
            ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
      else 1) ≤
      ∫ x in (0 : ℝ)..n, sharpUcbSummand ε a x := by
  have hshift :
      (∑ t ∈ Finset.Icc 1 n, sharpUcbSummand ε a t) =
        ∑ i ∈ Finset.Ico 0 n, sharpUcbSummand ε a (i + 1) := by
    have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext t
      simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_add_one_iff]
    rw [hIcc]
    symm
    simpa only [Nat.zero_add, Nat.cast_add, Nat.cast_one] using
      Finset.sum_Ico_add'
        (fun t : ℕ ↦ sharpUcbSummand ε a t) 0 n 1
  calc
    _ = ∑ t ∈ Finset.Icc 1 n, sharpUcbSummand ε a t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact sharpUcbSummand_nat_eq (Finset.mem_Icc.mp ht).1 ha
    _ = ∑ i ∈ Finset.Ico 0 n, sharpUcbSummand ε a (i + 1) := hshift
    _ ≤ ∫ x in (0 : ℝ)..n, sharpUcbSummand ε a x := by
      convert AntitoneOn.sum_le_integral_Ico (Nat.zero_le n)
        ((sharpUcbSummand_antitone hε ha).mono
          (fun x hx ↦ by simpa using hx.1)) using 1 <;>
        norm_num

lemma gaussian_substitution_image_Ioi {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    (fun s : ℝ ↦ ((s + Real.sqrt (2 * a)) / ε) ^ 2) '' Set.Ioi 0 =
      Set.Ioi (2 * a / ε ^ 2) := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hq : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hs0 : 0 < s := hs
    have hq_sq : Real.sqrt (2 * a) ^ 2 = 2 * a :=
      Real.sq_sqrt (by positivity)
    change 2 * a / ε ^ 2 <
      ((s + Real.sqrt (2 * a)) / ε) ^ 2
    rw [div_pow, div_lt_div_iff_of_pos_right hε2]
    nlinarith
  · intro hy
    change 2 * a / ε ^ 2 < y at hy
    have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hq : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
    have hq_sq : Real.sqrt (2 * a) ^ 2 = 2 * a :=
      Real.sq_sqrt (by positivity)
    have hcutpos : 0 < 2 * a / ε ^ 2 := by positivity
    have hypos : 0 < y := hcutpos.trans hy
    have hsqrty_sq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hypos.le
    have hmain : 2 * a < ε ^ 2 * y := by
      rw [div_lt_iff₀ hε2] at hy
      simpa [mul_comm] using hy
    have hepssqrt : 0 < ε * Real.sqrt y := mul_pos hε (Real.sqrt_pos.2 hypos)
    have hq_lt : Real.sqrt (2 * a) < ε * Real.sqrt y := by
      nlinarith [sq_nonneg (ε * Real.sqrt y + Real.sqrt (2 * a))]
    refine ⟨ε * Real.sqrt y - Real.sqrt (2 * a), sub_pos.mpr hq_lt, ?_⟩
    congr 1
    field_simp [ne_of_gt hε]
    nlinarith

lemma gaussian_substitution_injOn_Ioi {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    Set.InjOn (fun s : ℝ ↦ ((s + Real.sqrt (2 * a)) / ε) ^ 2)
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hq : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  have hxbase : 0 < (x + Real.sqrt (2 * a)) / ε :=
    div_pos (add_pos hx0 hq) hε
  have hybase : 0 < (y + Real.sqrt (2 * a)) / ε :=
    div_pos (add_pos hy0 hq) hε
  change ((x + Real.sqrt (2 * a)) / ε) ^ 2 =
    ((y + Real.sqrt (2 * a)) / ε) ^ 2 at hxy
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with heq | heq
  · field_simp [ne_of_gt hε] at heq
    linarith
  · nlinarith

lemma gaussian_substitution_tail_integrand {ε a s : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (hs : 0 < s) :
    Real.exp (-((ε * Real.sqrt
          (((s + Real.sqrt (2 * a)) / ε) ^ 2) -
        Real.sqrt (2 * a)) ^ 2) / 2) =
      Real.exp (-(1 / 2 : ℝ) * s ^ 2) := by
  have hq : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  have hbase : 0 ≤ (s + Real.sqrt (2 * a)) / ε := by positivity
  rw [Real.sqrt_sq hbase]
  congr 1
  field_simp [ne_of_gt hε]
  ring

lemma shifted_gaussian_integrableOn {a : ℝ} :
    IntegrableOn
      (fun s : ℝ ↦
        (s + Real.sqrt (2 * a)) * Real.exp (-(1 / 2 : ℝ) * s ^ 2))
      (Set.Ioi 0) := by
  have h₁ := integrable_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ) < 1 / 2)
  have h₂ := (integrable_exp_neg_mul_sq
    (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (Real.sqrt (2 * a))
  have hadd := h₁.add h₂
  apply hadd.integrableOn.congr_fun
  · intro s hs
    simp only [Pi.add_apply]
    ring
  · exact measurableSet_Ioi

lemma gaussian_tail_integrableOn {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ ↦
        Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2))
      (Set.Ioi (2 * a / ε ^ 2)) := by
  let f : ℝ → ℝ := fun s ↦ ((s + Real.sqrt (2 * a)) / ε) ^ 2
  let f' : ℝ → ℝ := fun s ↦ 2 * (s + Real.sqrt (2 * a)) / ε ^ 2
  let g : ℝ → ℝ := fun x ↦
    Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2)
  have hderiv : ∀ s ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt f (f' s) (Set.Ioi 0) s := by
    intro s hs
    exact (gaussian_substitution_hasDerivAt_sharp
      (a := a) (s := s) hε).hasDerivWithinAt
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hderiv (gaussian_substitution_injOn_Ioi hε ha) g
  rw [gaussian_substitution_image_Ioi hε ha] at hiff
  apply hiff.mpr
  have hbase := (shifted_gaussian_integrableOn (a := a)).const_mul
    (2 / ε ^ 2)
  apply hbase.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  have hq : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  have hfp : 0 < f' s := by
    dsimp [f']
    exact div_pos (mul_pos (by norm_num) (add_pos hs0 hq)) (sq_pos_of_pos hε)
  dsimp [f', g, f]
  rw [abs_of_pos hfp, gaussian_substitution_tail_integrand hε ha hs0]
  ring

lemma gaussian_tail_integral_closed {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∫ x in Set.Ioi (2 * a / ε ^ 2),
        Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2) =
      2 / ε ^ 2 * (1 + Real.sqrt (Real.pi * a)) := by
  let f : ℝ → ℝ := fun s ↦ ((s + Real.sqrt (2 * a)) / ε) ^ 2
  let f' : ℝ → ℝ := fun s ↦ 2 * (s + Real.sqrt (2 * a)) / ε ^ 2
  let g : ℝ → ℝ := fun x ↦
    Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2)
  have hderiv : ∀ s ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt f (f' s) (Set.Ioi 0) s := by
    intro s hs
    exact (gaussian_substitution_hasDerivAt_sharp
      (a := a) (s := s) hε).hasDerivWithinAt
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv (gaussian_substitution_injOn_Ioi hε ha) g
  rw [gaussian_substitution_image_Ioi hε ha] at hchange
  calc
    ∫ x in Set.Ioi (2 * a / ε ^ 2),
        Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2) =
        ∫ s in Set.Ioi 0,
          (2 / ε ^ 2) *
            ((s + Real.sqrt (2 * a)) *
              Real.exp (-(1 / 2 : ℝ) * s ^ 2)) := by
      rw [hchange]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hs0 : 0 < s := hs
      have hq : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
      have hfp : 0 < f' s := by
        dsimp [f']
        exact div_pos (mul_pos (by norm_num) (add_pos hs0 hq)) (sq_pos_of_pos hε)
      dsimp [f', g, f]
      rw [abs_of_pos hfp, gaussian_substitution_tail_integrand hε ha hs0]
      ring
    _ = 2 / ε ^ 2 *
        ∫ s in Set.Ioi 0,
          ((s + Real.sqrt (2 * a)) *
            Real.exp (-(1 / 2 : ℝ) * s ^ 2)) := by
      rw [← integral_const_mul]
    _ = 2 / ε ^ 2 * (1 + Real.sqrt (Real.pi * a)) := by
      rw [integral_shifted_gaussian_closed_sharp]

lemma sharpUcbSummand_integrableOn_Ioi {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    IntegrableOn (sharpUcbSummand ε a) (Set.Ioi 0) := by
  let c : ℝ := 2 * a / ε ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hhead : IntegrableOn (sharpUcbSummand ε a) (Set.Ioc 0 c) := by
    have hconst : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Ioc 0 c) :=
      integrableOn_const measure_Ioc_lt_top.ne
    apply hconst.congr_fun
    · intro x hx
      unfold sharpUcbSummand
      rw [if_pos]
      exact hx.2
    · exact measurableSet_Ioc
  have htail : IntegrableOn (sharpUcbSummand ε a) (Set.Ioi c) := by
    have h := gaussian_tail_integrableOn hε ha
    apply h.congr_fun
    · intro x hx
      unfold sharpUcbSummand
      rw [if_neg (not_le_of_gt hx)]
    · exact measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hc]
  exact hhead.union htail

lemma sharpUcbSummand_integral_Ioi_closed
    {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∫ x in Set.Ioi 0, sharpUcbSummand ε a x =
      2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) := by
  let c : ℝ := 2 * a / ε ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hhead : IntegrableOn (sharpUcbSummand ε a) (Set.Ioc 0 c) := by
    exact (sharpUcbSummand_integrableOn_Ioi hε ha).mono_set
      (Set.Ioc_subset_Ioi_self)
  have htail : IntegrableOn (sharpUcbSummand ε a) (Set.Ioi c) := by
    exact (sharpUcbSummand_integrableOn_Ioi hε ha).mono_set
      (Set.Ioi_subset_Ioi hc)
  rw [← Set.Ioc_union_Ioi_eq_Ioi hc]
  rw [setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hhead htail]
  have hhead_value :
      ∫ x in Set.Ioc 0 c, sharpUcbSummand ε a x = c := by
    calc
      ∫ x in Set.Ioc 0 c, sharpUcbSummand ε a x =
          ∫ _x in Set.Ioc 0 c, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        unfold sharpUcbSummand
        rw [if_pos hx.2]
      _ = c := by simp [Real.volume_Ioc, hc]
  have htail_value :
      ∫ x in Set.Ioi c, sharpUcbSummand ε a x =
        2 / ε ^ 2 * (1 + Real.sqrt (Real.pi * a)) := by
    calc
      ∫ x in Set.Ioi c, sharpUcbSummand ε a x =
          ∫ x in Set.Ioi (2 * a / ε ^ 2),
            Real.exp (-((ε * Real.sqrt x - Real.sqrt (2 * a)) ^ 2) / 2) := by
        dsimp [c]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        unfold sharpUcbSummand
        rw [if_neg (not_le_of_gt hx)]
      _ = _ := gaussian_tail_integral_closed hε ha
  rw [hhead_value, htail_value]
  dsimp [c]
  ring

lemma sharpUcbSummand_intervalIntegral_le
    (n : ℕ) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..n, sharpUcbSummand ε a x) ≤
      ∫ x in Set.Ioi 0, sharpUcbSummand ε a x := by
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ n)]
  apply setIntegral_mono_set (sharpUcbSummand_integrableOn_Ioi hε ha)
  · exact Filter.Eventually.of_forall fun x ↦ sharpUcbSummand_nonneg ε a x
  · exact Filter.Eventually.of_forall fun x hx ↦ hx.1

theorem bandit_ucb_index_exponential_sum_bound_sharp_proof
    {n : ℕ} {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    (∑ t ∈ Finset.Icc 1 n,
      if 2 * a / ε ^ 2 < (t : ℝ) then
        Real.exp (-((t : ℝ) * (ε - Real.sqrt (2 * a / t))) ^ 2 /
          ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
      else 1) ≤
      2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) := by
  calc
    _ ≤ ∫ x in (0 : ℝ)..n, sharpUcbSummand ε a x :=
      sharpUcbSummand_sum_le_intervalIntegral n hε ha
    _ ≤ ∫ x in Set.Ioi 0, sharpUcbSummand ε a x :=
      sharpUcbSummand_intervalIntegral_le n hε ha
    _ = 2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) :=
      sharpUcbSummand_integral_Ioi_closed hε ha

end BanditAlgorithm

theorem solution
    {n : ℕ} {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    (∑ t ∈ Finset.Icc 1 n,
      if 2 * a / ε ^ 2 < (t : ℝ) then
        Real.exp (-((t : ℝ) * (ε - Real.sqrt (2 * a / t))) ^ 2 /
          ((2 : ℝ) * (t : ℝ) * (1 : ℝ)))
      else 1) ≤
      2 / ε ^ 2 * (a + Real.sqrt (Real.pi * a) + 1) :=
  BanditAlgorithm.bandit_ucb_index_exponential_sum_bound_sharp_proof hε ha
