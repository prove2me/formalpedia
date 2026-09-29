-- Prove2me | Theorems.Thm_lean_workbook_plus_74198
-- name    : lean_workbook_plus_74198
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e63d2071-cfa4-4097-bd5c-a8bc636dd824
-- statement:
--   Since this is remainder from dividing by $10$ , we just need to find the units digit of $2^{400}$ . The units digit cycles in fours: $2,4,8,6$ . Since $400$ leaves a remainder of $0$ when divided by $4$ , the units digit is $6$ . $\boxed{\text{D}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74198 :
  (2^400) % 10 = 6   :=  by sorry
