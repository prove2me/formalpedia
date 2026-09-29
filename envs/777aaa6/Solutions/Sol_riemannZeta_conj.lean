-- Prove2me | solution 1 for riemannZeta_conj
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T12:35:34.349398+00:00
-- url     : https://prove2.me/submissions/a7256b37-90ad-4c7a-aace-cba954e8aaa5

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

open Complex MeasureTheory Set HurwitzZeta Real

namespace ZetaConj

noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0

lemma conj_cpow_ofReal {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (starRingEnd ℂ) ((t : ℂ) ^ w) = (t : ℂ) ^ ((starRingEnd ℂ) w) := by
  have harg : ((t : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact fun h => Real.pi_ne_zero h.symm
  have h := Complex.cpow_conj (t : ℂ) w harg
  rw [Complex.conj_ofReal] at h
  exact h.symm

/-- The modified theta kernel is real-valued. -/
lemma conj_f_modif (t : ℝ) : (starRingEnd ℂ) (P.f_modif t) = P.f_modif t := by
  simp only [P, WeakFEPair.f_modif, hurwitzEvenFEPair, Pi.add_apply, Set.indicator_apply,
    Function.comp_apply, map_add]
  split_ifs <;> simp

lemma conj_div_two (s : ℂ) : (starRingEnd ℂ) (s / 2) = (starRingEnd ℂ) s / 2 := by
  rw [map_div₀, map_ofNat]

lemma mellin_f_modif_conj (w : ℂ) :
    mellin P.f_modif ((starRingEnd ℂ) w) = (starRingEnd ℂ) (mellin P.f_modif w) := by
  have h : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ ((starRingEnd ℂ) w - 1) • P.f_modif t
      = (starRingEnd ℂ) ((t : ℂ) ^ (w - 1) • P.f_modif t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [smul_eq_mul, smul_eq_mul, map_mul, conj_cpow_ofReal ht0, conj_f_modif, map_sub, map_one]
  rw [mellin, mellin]
  calc ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((starRingEnd ℂ) w - 1) • P.f_modif t
      = ∫ t in Ioi (0 : ℝ), (starRingEnd ℂ) ((t : ℂ) ^ (w - 1) • P.f_modif t) :=
        setIntegral_congr_fun measurableSet_Ioi h
    _ = (starRingEnd ℂ) (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) • P.f_modif t) := integral_conj

lemma completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta₀ s) := by
  have h1 : completedRiemannZeta₀ ((starRingEnd ℂ) s)
      = mellin P.f_modif ((starRingEnd ℂ) s / 2) / 2 := rfl
  have h2 : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [h1, h2, ← conj_div_two, mellin_f_modif_conj, conj_div_two]

lemma completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq, completedRiemannZeta₀_conj, map_sub,
    map_sub, map_div₀, map_div₀, map_one, map_sub, map_one]

lemma Gammaℝ_conj (s : ℂ) : Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul, ← Complex.Gamma_conj,
    conj_cpow_ofReal Real.pi_pos, conj_div_two, map_neg, conj_div_two]

/-- **Schwarz reflection for the Riemann zeta function**: `ζ (conj s) = conj (ζ s)`. -/
theorem zeta_conj (s : ℂ) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [map_zero, riemannZeta_zero, map_div₀, map_neg, map_one, map_ofNat]
  · have hs' : (starRingEnd ℂ) s ≠ 0 := by simpa using hs
    rw [riemannZeta_def_of_ne_zero hs, riemannZeta_def_of_ne_zero hs',
      completedRiemannZeta_conj, Gammaℝ_conj, map_div₀]


end ZetaConj

theorem solution (s : ℂ) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) :=
  ZetaConj.zeta_conj s
