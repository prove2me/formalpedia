-- Prove2me | solution 1 for Cryptography.IsogenySIDH.btNum_btDen_no_common_root
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:51:12.909384+00:00
-- url     : https://prove2.me/submissions/baacb734-52a8-4c15-9090-2f422f93484f

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_RadicalNonBacktracking
open Cryptography.IsogenySIDH in
theorem solution {K : Type*} [Field K] {A : K} (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (h5 : (5 : K) ≠ 0) (h11 : (11 : K) ≠ 0) (hn : btNum A = 0) (hd : btDen A = 0) :
    False := by
  unfold btNum at hn
  unfold btDen at hd
  have h4 : (4 : K) ≠ 0 := by
    have := mul_ne_zero h2 h2
    norm_num at this
    exact this
  -- `btDen A = 0` means `A² = 3` or `A = 2`
  have hd' : (A ^ 2 - 3) * (A - 2) = 0 := by
    have : (4 : K) * ((A ^ 2 - 3) * (A - 2)) = 0 := by rw [← hd]; ring
    exact (mul_eq_zero.mp this).resolve_left h4
  rcases mul_eq_zero.mp hd' with hA | hA
  · -- `A² = 3` and `A² + 60A + 132 = 0` force `7425 = 3³·5²·11 = 0`
    have h7425 : (7425 : K) = 0 := by
      linear_combination 3600 * hA - (60 * A - 135) * (hn - hA)
    have hfac : (7425 : K) = 3 ^ 3 * 5 ^ 2 * 11 := by norm_num
    rw [hfac] at h7425
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h3) (pow_ne_zero 2 h5)) h11 h7425
  · -- `A = 2` gives `btNum = 256 = 2⁸ ≠ 0`
    have hA2 : A = 2 := by linear_combination hA
    rw [hA2] at hn
    have h256 : (2 : K) ^ 8 = 0 := by linear_combination hn
    exact pow_ne_zero 8 h2 h256
