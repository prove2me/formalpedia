-- Prove2me | Theorems.Thm_lean_workbook_plus_40018
-- name    : lean_workbook_plus_40018
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9591fa4c-6c47-4da5-8be4-258ab81934f9
-- statement:
--   Prove that if $a\equiv19\pmod{30}$, then $3a\equiv7\pmod{10}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40018 : a ≡ 19 [ZMOD 30] → 3 * a ≡ 7 [ZMOD 10]   :=  by sorry
