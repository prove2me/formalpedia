-- Prove2me | solution 1 for EllipticModCount.cube_bijective_iff_char_neg_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:34:14.436924+00:00
-- url     : https://prove2.me/submissions/ffd30116-2edd-492b-a81b-06f9bcb14eff

import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticSecondMoment
import Definitions.Def_Combinatorics_EllipticVerticalMoment

open EllipticModCount Finset in
theorem solution {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (h3 : (3 : F) ≠ 0) :
    (Function.Bijective fun x : F => x ^ 3) ↔ quadraticChar F (-3) = -1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [quadraticChar_neg_one_iff_not_isSquare, ← Finite.injective_iff_bijective]
  constructor
  · -- a square root of `-3` produces a primitive cube root of unity
    rintro hinj ⟨s, hs⟩
    set ω : F := (-1 + s) / 2 with hωdef
    have h2ω : 2 * ω = -1 + s := by
      rw [hωdef]
      field_simp
    have h4 : 4 * (ω ^ 2 + ω + 1) = 0 := by
      linear_combination (2 * ω + (-1 + s) + 2) * h2ω - hs
    have h4ne : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    have hω : ω ^ 2 + ω + 1 = 0 := (mul_eq_zero.1 h4).resolve_left h4ne
    have hω3 : (fun x : F => x ^ 3) ω = (fun x : F => x ^ 3) 1 := by
      show ω ^ 3 = 1 ^ 3
      linear_combination (ω - 1) * hω
    have hω1 : ω = 1 := hinj hω3
    rw [hω1] at hω
    apply h3
    linear_combination hω
  · -- two distinct cubes that agree give a square root of `-3`
    intro hns x y hxy
    simp only at hxy
    by_contra hne
    apply hns
    have hq : x ^ 2 + x * y + y ^ 2 = 0 := by
      have h : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by linear_combination hxy
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hne)
    have hy : y ≠ 0 := by
      rintro rfl
      apply hne
      simpa using hq
    have hsq : (2 * x + y) ^ 2 = -3 * y ^ 2 := by linear_combination 4 * hq
    refine ⟨(2 * x + y) / y, ?_⟩
    rw [eq_comm, div_mul_div_comm, div_eq_iff (mul_ne_zero hy hy)]
    linear_combination hsq
