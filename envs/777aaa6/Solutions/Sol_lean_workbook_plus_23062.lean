-- Prove2me | solution 1 for lean_workbook_plus_23062
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:29.639129+00:00
-- url     : https://prove2.me/submissions/d752a8d6-8616-4e31-9816-6c811af310c6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (y : ℝ)
  (n : ℤ)
  (h₀ : n ≤ y)
  (h₁ : y < n + 1 / 2) :
  Int.floor (y + 1) + Int.floor y = Int.floor (2 * y + 1) := by
  have hf : Int.floor y=n := Int.floor_eq_iff.mpr ⟨h₀,by linarith⟩
  have hf1 : Int.floor (y+1)=n+1 := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  have hf2 : Int.floor (2*y+1)=2*n+1 := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  rw [hf,hf1,hf2]
  ring
