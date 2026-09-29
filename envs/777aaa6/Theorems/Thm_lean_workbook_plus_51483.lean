-- Prove2me | Theorems.Thm_lean_workbook_plus_51483
-- name    : lean_workbook_plus_51483
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5d1e3f1a-e22c-4272-a415-b0c2a43c6571
-- statement:
--   Let us denote the number that is divisible by $10$ as $10a$ . Then, the unit digit is $0$ . If the units digit is removed, it is the same thing as dividing the number by $10$ . Therefore the two numbers are $10a$ and $a$ . Since $11a=17402 \implies a=1582$ , the $2$ numbers are $15820$ and $1582$ . $15820-1582=14238$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51483  (a : ℕ)
  (h₀ : 11 * a = 17402) :
  15820 - 1582 = 14238   :=  by sorry
