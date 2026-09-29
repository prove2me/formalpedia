-- Prove2me | solution 1 for lean_workbook_plus_1714
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:53:09.779428+00:00
-- url     : https://prove2.me/submissions/7719070e-7eb6-4231-a90c-b0c7ce35463e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : 2 ^ 2011 + 3 ^ 2011 + 4 ^ 2011 + 5 ^ 2011 + 6 ^ 2011 + 7 ^ 2011 + 8 ^ 2011 + 2011 ≡ 3 [ZMOD 9] := by
  have pair (a : ℤ) : a^2011 + (9-a)^2011 ≡ 0 [ZMOD 9] := by
    have h : 9-a ≡ -a [ZMOD 9] := by
      rw [Int.modEq_iff_dvd]
      use -1
      ring
    have hp := h.pow 2011
    have hn : (-a)^2011 = -(a^2011) := by
      rw [neg_pow]
      norm_num
    rw [hn] at hp
    have hh := (Int.ModEq.refl (a^2011)).add hp
    have hz : a^2011 + -(a^2011) = 0 := by omega
    rw [hz] at hh
    exact hh
  have h2 := pair 2
  have h3 := pair 3
  have h4 := pair 4
  change (2:ℤ)^2011 + 7^2011 ≡ 0 [ZMOD 9] at h2
  change (3:ℤ)^2011 + 6^2011 ≡ 0 [ZMOD 9] at h3
  change (4:ℤ)^2011 + 5^2011 ≡ 0 [ZMOD 9] at h4
  have h8 : (8:ℤ)^2011 ≡ -1 [ZMOD 9] := by
    have h := (show (8:ℤ) ≡ -1 [ZMOD 9] from by norm_num [Int.ModEq]).pow 2011
    simpa only [show (-1:ℤ)^2011 = -1 by norm_num] using h
  have hc : (2011:ℤ) ≡ 4 [ZMOD 9] := by norm_num [Int.ModEq]
  have h := (((h2.add h3).add h4).add h8).add hc
  have rearrange (a b c d e f g z : ℤ) :
    a+b+c+d+e+f+g+z = ((a+f)+(b+e)+(c+d))+g+z := by abel
  rw [rearrange]
  exact h
