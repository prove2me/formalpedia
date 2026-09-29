-- Prove2me | solution 1 for mme_stothers_positive_slice_minimum_is_stationary
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-21T23:14:59.082144+00:00
-- url     : https://prove2.me/submissions/253d2d8b-25c4-463d-89ca-f606396cfe32

import Definitions.Def_mme_stothers_fourth_data
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

open MME.StothersFourth BigOperators Filter

set_option autoImplicit false

private theorem log_entropyProduct
    (b : Fin 10 → ℝ) (hb : ∀ i, 0 < b i) :
    Real.log (entropyProduct b) =
      ∑ i, (classMultiplicity i : ℝ) * b i * Real.log (b i) := by
  rw [entropyProduct, Real.log_prod
    (f := fun i ↦ Real.rpow (b i) ((classMultiplicity i : ℝ) * b i))
    (fun i _ ↦ (Real.rpow_pos_of_pos (hb i) _).ne')]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.log_rpow (hb i) _

/-- A positive slice minimizer has zero entropy derivative in each feasible direction. -/
private theorem entropy_direction_eq_zero
    (b d : Fin 10 → ℝ)
    (hb : InZ b) (hbpos : ∀ i, 0 < b i)
    (hd : InY d)
    (hweight : ∑ i, (classMultiplicity i : ℝ) * d i = 0)
    (hmin : ∀ c : Fin 10 → ℝ, InZ c →
      InY (fun i ↦ c i - b i) → entropyProduct b ≤ entropyProduct c) :
    ∑ i, (classMultiplicity i : ℝ) * d i * (Real.log (b i) + 1) = 0 := by
  let f : ℝ → ℝ := fun t ↦
    ∑ i, (classMultiplicity i : ℝ) * (b i + t * d i) *
      Real.log (b i + t * d i)
  have hpos : ∀ᶠ t : ℝ in nhds 0, ∀ i, 0 < b i + t * d i := by
    rw [eventually_all]
    intro i
    have hc : ContinuousAt (fun t : ℝ ↦ b i + t * d i) 0 := by fun_prop
    simpa using hc.eventually (Ioi_mem_nhds (by simpa using hbpos i))
  have hlocal : IsLocalMin f 0 := by
    filter_upwards [hpos] with t ht
    have hc : InZ (fun i ↦ b i + t * d i) := by
      refine ⟨fun i ↦ (ht i).le, ?_⟩
      simp only [mul_add, Finset.sum_add_distrib]
      simp_rw [← mul_assoc, mul_comm _ t, mul_assoc]
      rw [← Finset.mul_sum, hweight, mul_zero, add_zero]
      exact hb.2
    have hdir : InY (fun i ↦ (b i + t * d i) - b i) := by
      obtain ⟨s, u, hsu⟩ := hd
      refine ⟨t * s, t * u, fun i ↦ ?_⟩
      dsimp
      rw [hsu i]
      ring
    have he := Real.log_le_log (show 0 < entropyProduct b from
      Finset.prod_pos (fun i _ ↦ Real.rpow_pos_of_pos (hbpos i) _)) (hmin _ hc hdir)
    rw [log_entropyProduct b hbpos, log_entropyProduct _ ht] at he
    simpa [f] using he
  have hderiv : HasDerivAt f
      (∑ i, (classMultiplicity i : ℝ) * d i * (Real.log (b i) + 1)) 0 := by
    apply HasDerivAt.congr_deriv (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
      (((hasDerivAt_id (0 : ℝ)).mul_const (d i)).const_add (b i) |>.const_mul
        (classMultiplicity i : ℝ)).mul
        ((((hasDerivAt_id (0 : ℝ)).mul_const (d i)).const_add (b i)).log
          (by simpa using (hbpos i).ne'))))
    apply Finset.sum_congr rfl
    intro i _
    simp only [id_eq, zero_mul, add_zero, one_mul]
    field_simp [(hbpos i).ne']
  exact hderiv.deriv.symm.trans hlocal.deriv_eq_zero

/-- Positivity makes both kernel directions available at an entropy minimum. -/
theorem solution
    (b : Fin 10 → ℝ) (hb : InZ b) (hbpos : ∀ i, 0 < b i)
    (hmin : ∀ c : Fin 10 → ℝ, InZ c →
      InY (fun i ↦ c i - b i) → entropyProduct b ≤ entropyProduct c) :
    InN b := by
  have hs := entropy_direction_eq_zero b kernelSigma hb hbpos
    ⟨1, 0, by intro i; simp⟩
    (by norm_num [classMultiplicity, kernelSigma, Fin.sum_univ_succ]
        change (-2 : ℝ) + 2 = 0
        norm_num) hmin
  have ht := entropy_direction_eq_zero b kernelTau hb hbpos
    ⟨0, 1, by intro i; simp⟩
    (by norm_num [classMultiplicity, kernelTau, Fin.sum_univ_succ]) hmin
  norm_num [classMultiplicity, kernelSigma, Fin.sum_univ_succ] at hs
  norm_num [classMultiplicity, kernelTau, Fin.sum_univ_succ] at ht
  change 2 * (Real.log (b 2) + 1) +
    (-(2 * (Real.log (b 4) + 1)) + (-(2 * (Real.log (b 5) + 1)) +
    (4 * (Real.log (b 7) + 1) + -(2 * (Real.log (b 9) + 1))))) = 0 at hs
  change 2 * (Real.log (b 3) + 1) +
    (-(2 * (Real.log (b 4) + 1)) + (-(2 * (Real.log (b 6) + 1)) +
    (2 * (Real.log (b 7) + 1) + (2 * (Real.log (b 8) + 1) +
    -(2 * (Real.log (b 9) + 1)))))) = 0 at ht
  refine ⟨hb, ?_, ?_⟩
  · apply Real.log_injOn_pos
      (mul_pos (hbpos 2) (pow_pos (hbpos 7) 2))
      (mul_pos (mul_pos (hbpos 4) (hbpos 5)) (hbpos 9))
    rw [Real.log_mul (hbpos 2).ne' (pow_pos (hbpos 7) 2).ne',
      Real.log_mul (mul_pos (hbpos 4) (hbpos 5)).ne' (hbpos 9).ne',
      Real.log_mul (hbpos 4).ne' (hbpos 5).ne', Real.log_pow]
    norm_num
    linarith
  · apply Real.log_injOn_pos
      (mul_pos (mul_pos (hbpos 3) (hbpos 7)) (hbpos 8))
      (mul_pos (mul_pos (hbpos 4) (hbpos 6)) (hbpos 9))
    rw [Real.log_mul (mul_pos (hbpos 3) (hbpos 7)).ne' (hbpos 8).ne',
      Real.log_mul (hbpos 3).ne' (hbpos 7).ne',
      Real.log_mul (mul_pos (hbpos 4) (hbpos 6)).ne' (hbpos 9).ne',
      Real.log_mul (hbpos 4).ne' (hbpos 6).ne']
    linarith
