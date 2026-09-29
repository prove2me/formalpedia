-- Prove2me | Theorems.Thm_lean_workbook_plus_7894
-- name    : lean_workbook_plus_7894
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a77da89a-e3e4-4fdc-a4dd-5dc95f9f8a87
-- statement:
--   Now, we say that $ x=3+40a$ and $ x=4+7b$ . So, we obtain that $ 3+40a=4+7b$ , giving that $ 7b+1=40a$ , so $ 7b+1\equiv 0\bmod 40$ and therefore that $ 7b\equiv 39\bmod 40$ . Thus, we can show that $ b\equiv 17\bmod 40$ . We say that $ b=17+40c$ and plug it in to get that $ x=4+7b=4+7(40c+17)=123+280c$ , so $ \boxed{x\equiv 123\bmod 280}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7894  (x a b c : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : x = 3 + 40 * a)
  (h₂ : x = 4 + 7 * b)
  (h₃ : b = 17 + 40 * c) :
  x ≡ 123 [MOD 280]   :=  by sorry
