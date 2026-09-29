-- Prove2me | solution 1 for mme_Ctensor_one_H_one_outer_family_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T04:47:37.911574+00:00
-- url     : https://prove2.me/submissions/ca6ae243-cb88-43a7-8632-a5a2827a7449

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_balanced_extractions_sqrt_loss
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
        (((volume ^ 3 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast (cyclicSymmetrization T) tau V := by
  let B : ℝ :=
    (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
      (((volume ^ 3 : ℕ) : ℝ) ^ tau)
  have hVB : V < B := by simpa [B] using hVlt
  have hA : 0 < A := by
    by_contra h
    have hzero : A = 0 := Nat.eq_zero_of_not_pos h
    subst A
    simp at hVlt
    linarith
  have hH : 0 < H := by
    by_contra h
    have hzero : H = 0 := Nat.eq_zero_of_not_pos h
    subst H
    simp at hVlt
    linarith
  have htau_pos : 0 < tau := by linarith
  have hvolume : 0 < volume := by
    by_contra h
    have hzero : volume = 0 := Nat.eq_zero_of_not_pos h
    subst volume
    simp [Real.zero_rpow htau_pos.ne'] at hVlt
    linarith
  obtain ⟨C, hC, hfinite⟩ :=
    mme_Ctensor_one_H_one_outer_family_balanced_extractions_sqrt_loss
      stars hA hH hvolume tau htau
  let s : ℕ → ℕ := fun m => A ^ 3 * H * m
  have hAH : 0 < A ^ 3 * H := Nat.mul_pos (pow_pos hA 3) hH
  have hs : Tendsto s atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    dsimp [s]
    exact hm.trans (by
      simpa [mul_comm] using Nat.le_mul_of_pos_right m hAH)
  have hgap0 :=
    mme_strict_pow_absorbs_sqrt_exp_loss V B C hV hVB hC
  have hgap :
      ∀ᶠ m : ℕ in atTop,
        V ^ (s m) ≤ B ^ (s m) *
          Real.exp
            (-C * Real.sqrt ((((s m) + 1 : ℕ) : ℝ))) :=
    hs.eventually hgap0
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (T := cyclicSymmetrization T) tau V hV s hs
    (fun _ => (0 : ℝ)) tendsto_const_nhds
  filter_upwards [hfinite, hgap] with m hm hmgap
  dsimp only at hm
  obtain ⟨k, a, b, c, hrestrict, hcount⟩ := hm
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  simp only [sub_zero, mul_one]
  exact hmgap.trans (by
    change B ^ (s m) *
        Real.exp
          (-C * Real.sqrt ((((s m) + 1 : ℕ) : ℝ))) ≤
      ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)
    simpa [B, s] using hcount)
