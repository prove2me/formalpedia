-- Prove2me | solution 1 for Cryptography.IsogenySIDH.radical_two_step_nonbacktracking_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:55:48.970182+00:00
-- url     : https://prove2.me/submissions/01de4a2d-b459-4a34-bca7-cd2cad195f70

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
import Definitions.Def_Cryptography_IsogenySIDH_RadicalNonBacktracking
open Cryptography.IsogenySIDH in
theorem solution {K : Type*} [Field K] {A α : K} (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) (h5 : (5 : K) ≠ 0) (h11 : (11 : K) ≠ 0)
    (hcube : ∀ t : K, t ^ 2 + t + 1 ≠ 0) (hα : α ≠ 0) (hsq : α ^ 2 = A + 2)
    (hd : A ^ 2 - 4 ≠ 0) (hj1 : jMont A ≠ -3375) (hj2 : jMont A ≠ 287496) :
    jQuot (radTwoParam A α) ≠ jMont A := by
  have h4 : (4 : K) ≠ 0 := by
    have := mul_ne_zero h2 h2
    norm_num at this
    exact this
  have hAp : A + 2 ≠ 0 := by
    rw [← hsq]
    exact pow_ne_zero 2 hα
  have hAm : A - 2 ≠ 0 := by
    intro h0
    apply hd
    have : A = 2 := by linear_combination h0
    rw [this]
    norm_num
  -- no common root of `btNum`, `btDen`
  have hnc : ¬ (btNum A = 0 ∧ btDen A = 0) := by
    rintro ⟨hn, hd'⟩
    unfold btNum at hn
    unfold btDen at hd'
    have hd'' : (A ^ 2 - 3) * (A - 2) = 0 := by
      have : (4 : K) * ((A ^ 2 - 3) * (A - 2)) = 0 := by rw [← hd']; ring
      exact (mul_eq_zero.mp this).resolve_left h4
    rcases mul_eq_zero.mp hd'' with hA | hA
    · have h7425 : (7425 : K) = 0 := by
        linear_combination 3600 * hA - (60 * A - 135) * (hn - hA)
      have hfac : (7425 : K) = 3 ^ 3 * 5 ^ 2 * 11 := by norm_num
      rw [hfac] at h7425
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h3) (pow_ne_zero 2 h5)) h11 h7425
    · exact hAm hA
  intro hj
  -- `jQuot B = jMont A` is equivalent to `btNum³ = btDen³`
  have hB2 : ((A + 6) / (2 * α)) ^ 2 = (A + 6) ^ 2 / (4 * (A + 2)) := by
    rw [div_pow, mul_pow, hsq]
    norm_num
  have hcubes : btNum A ^ 3 = btDen A ^ 3 := by
    unfold jQuot jMont radTwoParam at hj
    rw [hB2] at hj
    unfold btNum btDen
    have hd2 : A ^ 2 - 4 = (A - 2) * (A + 2) := by ring
    rw [hd2] at hj
    have hden1 : (A + 6) ^ 2 / (4 * (A + 2)) - 4 = (A - 2) ^ 2 / (4 * (A + 2)) := by
      field_simp
      ring
    have hnum1 : (A + 6) ^ 2 / (4 * (A + 2)) + 12 = (A ^ 2 + 60 * A + 132) / (4 * (A + 2)) := by
      field_simp
      ring
    rw [hden1, hnum1] at hj
    field_simp at hj
    have h16 : (16 : K) ≠ 0 := by
      have := mul_ne_zero h4 h4
      norm_num at this
      exact this
    apply mul_left_cancel₀ h16
    linear_combination hj
  -- factor the difference of cubes
  have hfact : btNum A ^ 3 - btDen A ^ 3
      = -(A - 6) * (4 * A ^ 2 + 15 * A + 18) *
          (btNum A ^ 2 + btNum A * btDen A + btDen A ^ 2) := by
    unfold btNum btDen
    ring
  have hzero : -(A - 6) * (4 * A ^ 2 + 15 * A + 18) *
      (btNum A ^ 2 + btNum A * btDen A + btDen A ^ 2) = 0 := by
    rw [← hfact, hcubes, sub_self]
  rcases mul_eq_zero.mp hzero with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · -- `A = 6` has `j = 287496`
      have hA6 : A = 6 := by linear_combination -h''
      apply hj2
      rw [hA6]
      unfold jMont
      have h32 : (6 : K) ^ 2 - 4 ≠ 0 := by
        have : (6 : K) ^ 2 - 4 = 2 ^ 5 := by norm_num
        rw [this]
        exact pow_ne_zero 5 h2
      rw [div_eq_iff h32]
      norm_num
    · -- `4A² + 15A + 18 = 0` has `j = -3375`
      apply hj1
      unfold jMont
      rw [div_eq_iff hd]
      linear_combination (64 * A ^ 4 - 240 * A ^ 3 + 36 * A ^ 2 + 945 * A - 1134) * h''
  · -- the cube-root branch: needs a primitive cube root of unity, or a common root
    by_cases hD : btDen A = 0
    · have hN : btNum A = 0 := by
        rw [hD] at h'
        have : btNum A ^ 2 = 0 := by linear_combination h'
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      exact hnc ⟨hN, hD⟩
    · apply hcube (btNum A / btDen A)
      field_simp
      linear_combination h'
