-- Prove2me | Theorems.Thm_lean_workbook_plus_7278
-- name    : lean_workbook_plus_7278
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/11dec200-c15a-4e2a-a152-e543b28c9ce5
-- statement:
--   Now we have $8^{\log_{2} \sqrt{6}}$ . If we rewrite $8$ as $2^3$ , the expression rewrites as $(2^3)^{\log_{2} \sqrt{6}}=2^{3\log_{2}\sqrt{6}}=2^{\log_{2} (\sqrt{6})^3}=(\sqrt{6})^3=6\sqrt{6}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7278 :
  8^Real.logb 2 (Real.sqrt 6) = 6 * Real.sqrt 6   :=  by sorry
