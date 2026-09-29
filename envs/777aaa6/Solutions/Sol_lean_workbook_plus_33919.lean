-- Prove2me | solution 1 for lean_workbook_plus_33919
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:59:51.937032+00:00
-- url     : https://prove2.me/submissions/1601e65a-17da-4d3c-a7cf-0c28fe148675

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n x a : ℕ) (h₁ : 10^(n-1) > x ∧ x ≥ 10^(n-2)) (h₂ : a ∈ Finset.range 10) (h₃ : a*10^(n-1) + x = 9*(10*x + a)) : 89*x = a*(10^(n-1) - 9) := by
  have hx : 0<x := lt_of_lt_of_le (pow_pos (by norm_num) _) h₁.2
  have ha : 0<a := by
    by_contra hn
    have he : a=0 := by omega
    simp [he] at h₃
    omega
  have ht : 9 ≤ 10^(n-1) := by
    by_contra hn
    have hm := Nat.mul_le_mul_left a (show 10^(n-1) ≤ 8 by omega)
    nlinarith
  have he : a*10^(n-1)=89*x+9*a := by nlinarith
  rw [Nat.mul_sub_left_distrib,he]
  omega
