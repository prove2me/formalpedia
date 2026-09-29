-- Prove2me | solution 1 for lean_workbook_plus_33041
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:43:19.257713+00:00
-- url     : https://prove2.me/submissions/8bc25f5d-f501-42d1-9e4c-891092a27c08

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (k : ℕ) (h₁ : 1.4 < x ∧ x < 1.6) (h₂ : 3 ≤ k) : ⌊x + 1 / k⌋ = 1 := by
  have hk : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h₂
  have hi : (1 : ℝ) / (k : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hk
  have hn : 0 ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg k)
  apply Int.floor_eq_iff.mpr
  norm_num [one_div] at hi ⊢
  constructor <;> linarith [h₁.1, h₁.2]
