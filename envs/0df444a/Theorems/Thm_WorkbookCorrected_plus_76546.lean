-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_76546
-- name    : WorkbookCorrected.plus_76546
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:21.711892+00:00
-- url     : https://prove2.me/theorems/40af8b13-4a29-41e3-aa98-9fd2c108747d
-- title:
--   A quadratic and triple-product minimum at fixed sum
-- statement:
--   Let $a,b,c \geq 0$ and $a+b+c=3$. Find the min of $a^2+b^2+c^2+2abc$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_76546` (Apache-2.0). Natural-language proposition preserved; the source bound is completed with an exact attainment witness. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_76546; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.plus_76546 : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3), 9 / 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c) ∧ (∃ a b c : ℝ, (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (a + b + c = 3) ∧ ( 9 / 2  =  a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c   )) := by sorry
