-- Prove2me | Theorems.Thm_lean_workbook_plus_55641
-- name    : lean_workbook_plus_55641
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/25320e62-d1a0-4054-9dfc-9abcb2037f40
-- statement:
--   $(7! \cdot 4!)\binom {4+5-1}{5-1}=7! \cdot 4! \cdot 70$ and I don't wanna compute. Just basic stars and bars.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55641 (7! * 4! * 70) = (7! * 4! * choose (4+5-1) (5-1))   :=  by sorry
