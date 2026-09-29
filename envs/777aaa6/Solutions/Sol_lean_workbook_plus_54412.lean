-- Prove2me | solution 1 for lean_workbook_plus_54412
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:11:30.367423+00:00
-- url     : https://prove2.me/submissions/da803b2c-85f2-4704-b512-d0b08ebd0836

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℤ) (h₁ : x^2 + y^2 = z^2) (h₂ : Odd x ∧ Odd y) : False := by
  have sourceClaim (u v w : ℤ) (heq : u^2+v^2=w^2) :
      ¬ (Odd u ∧ Odd v) ∧ (6:ℤ) ∣ u*v := by
    have square4 (t : ℤ) : t^2 % 4 = 0 ∨ t^2 % 4 = 1 := by
      have hlo := Int.emod_nonneg t (by decide : (4:ℤ) ≠ 0)
      have hhi := Int.emod_lt_of_pos t (by decide : (0:ℤ) < 4)
      rw [pow_two,Int.mul_emod]
      interval_cases h : t%4 <;> norm_num [h]
    have oddSquare4 (t : ℤ) (ht : Odd t) : t^2 % 4 = 1 := by
      obtain ⟨k,hk⟩ := ht
      have hid : t^2 = 4*(k^2+k)+1 := by rw [hk]; ring
      rw [hid]
      omega
    have hnot : ¬ (Odd u ∧ Odd v) := by
      intro hodd
      have hu := oddSquare4 u hodd.1
      have hv := oddSquare4 v hodd.2
      have hw := square4 w
      have hm := congrArg (fun t:ℤ => t%4) heq
      dsimp only at hm
      rw [Int.add_emod,hu,hv] at hm
      omega
    have h2 : (2:ℤ) ∣ u*v := by
      apply even_iff_two_dvd.mp
      apply Int.not_odd_iff_even.mp
      intro hodd
      exact hnot (Int.odd_mul.mp hodd)
    have h3 : (3:ℤ) ∣ u*v := by
      apply Int.dvd_iff_emod_eq_zero.mpr
      have hm := congrArg (fun t:ℤ => t%3) heq
      simp only [Int.add_emod,pow_two,Int.mul_emod,Int.emod_emod] at hm
      rw [Int.mul_emod]
      have hu0 := Int.emod_nonneg u (by decide : (3:ℤ) ≠ 0)
      have hu3 := Int.emod_lt_of_pos u (by decide : (0:ℤ) < 3)
      have hv0 := Int.emod_nonneg v (by decide : (3:ℤ) ≠ 0)
      have hv3 := Int.emod_lt_of_pos v (by decide : (0:ℤ) < 3)
      have hw0 := Int.emod_nonneg w (by decide : (3:ℤ) ≠ 0)
      have hw3 := Int.emod_lt_of_pos w (by decide : (0:ℤ) < 3)
      interval_cases hu : u%3 <;> interval_cases hv : v%3 <;> interval_cases hw : w%3 <;>
        norm_num at hm <;> norm_num
    exact ⟨hnot,(show IsCoprime (2:ℤ) 3 from ⟨-1,1,by norm_num⟩).mul_dvd h2 h3⟩
  exact (sourceClaim x y z h₁).1 h₂
