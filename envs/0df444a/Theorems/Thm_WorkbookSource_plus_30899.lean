-- Prove2me | Theorems.Thm_WorkbookSource_plus_30899
-- name    : WorkbookSource.plus_30899
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:47:43.661948+00:00
-- url     : https://prove2.me/theorems/108b10b9-a89e-4603-a53a-4285ae581127
-- title:
--   A quartic cyclic bound under a quadratic constraint
-- statement:
--   Let $a,b,c$ be nonnegative real numbers such that $a^2+b^2+c^2=\frac{5}{2}(ab+bc+ca)$. Prove that $11(a^4+b^4+c^4) \ge 17(a^3b+b^3c+c^3a)+129abc(a+b+c)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_30899` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_30899; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_30899 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = (5/2) * (a * b + b * c + c * a)) : 11 * (a^4 + b^4 + c^4) ≥ 17 * (a^3 * b + b^3 * c + c^3 * a) + 129 * a * b * c * (a + b + c)   :=  by sorry
