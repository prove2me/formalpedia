-- Prove2me | Theorems.Thm_lean_workbook_plus_79679
-- name    : lean_workbook_plus_79679
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/789bf328-3215-465c-a0a4-b2f88a6c7bc8
-- statement:
--   Observe this in $ \pmod{10}$ . Reduce the 17 to 7 for easier arithmatic. Experiment with the first few powers, and find that $ 7^{4}\equiv{1}\pmod{10}$ . Now, take $ 7^{1996}$ and rewrite it as $ (7^4)^{499}$ . We now have $ 1^{499}\equiv{1}\pmod{10}$ . Therefore, the units digit is
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79679 :
  (7^1996) % 10 = 1   :=  by sorry
