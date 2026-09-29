-- Prove2me | solution 1 for lean_workbook_plus_35594
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:21.338501+00:00
-- url     : https://prove2.me/submissions/a9f8621c-977c-4ee4-aa74-054542c78dda

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p : ℕ) (k : ℕ) (h₁ : p * p ≤ k) (h₂ : k < (p + 1) * (p + 1)) : ⌊Real.sqrt k⌋ = p := by
  apply Int.floor_eq_iff.mpr
  have hk : 0 ≤ (k:ℝ) := by positivity
  have hs := Real.sq_sqrt hk
  have hn := Real.sqrt_nonneg (k:ℝ)
  have hp : 0 ≤ (p:ℝ) := by positivity
  have h1 : (p:ℝ)*(p:ℝ) ≤ (k:ℝ) := by exact_mod_cast h₁
  have h2 : (k:ℝ) < ((p:ℝ)+1)*((p:ℝ)+1) := by exact_mod_cast h₂
  constructor <;> push_cast <;> nlinarith
