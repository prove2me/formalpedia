-- Prove2me | solution 1 for lean_workbook_plus_60962
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:09:36.062195+00:00
-- url     : https://prove2.me/submissions/8cb36513-0d82-422b-a2e1-77391061c562

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℤ)
  (h₀ : Odd x ∧ Odd y)
  (h₁ : (x + 1) * (y + 1) ≡ 2 [ZMOD 4]) :
  False := by
  obtain ⟨u,hu⟩ := h₀.1
  obtain ⟨v,hv⟩ := h₀.2
  have hdiv : (4:ℤ) ∣ (x+1)*(y+1) := by
    use (u+1)*(v+1)
    rw [hu,hv]
    ring
  have hz := Int.modEq_zero_iff_dvd.mpr hdiv
  have hbad := hz.symm.trans h₁
  norm_num [Int.ModEq] at hbad
