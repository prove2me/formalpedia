-- Prove2me | solution 1 for lean_workbook_plus_51768
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:34:03.119548+00:00
-- url     : https://prove2.me/submissions/af966e41-52b9-40f2-9dd4-cf29b3951045

import Mathlib
set_option autoImplicit false

theorem solution  (a n : ℝ)
  (h₀ : 1 < a)
  (h₁ : 0 < n) :
  1 / (a - 1) - 1 / (a + n) + 1 / (a + n + 1)^2 ≤ 1 / (a - 1) - 1 / (a + n + 1) ↔ (a + n + 2) * (a + n) ≤ (a + n + 1)^2   := by
  have ht : 0 < a + n := by linarith
  have ht1 : 0 < a + n + 1 := by linarith
  have hadd : 1 / (a + n + 1) + 1 / (a + n + 1)^2 =
      (a + n + 2) / (a + n + 1)^2 := by
    field_simp [ht1.ne'] <;> ring
  have hiff : ((a + n + 2) / (a + n + 1)^2 <= 1 / (a + n)) <->
      (a + n + 2) * (a + n) <= (a + n + 1)^2 := by
    rw [div_le_div_iff₀ (by positivity : 0 < (a + n + 1)^2) ht, one_mul]
  rw [<- hiff, <- hadd]
  constructor <;> intro h <;> linarith

#print axioms solution
