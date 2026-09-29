-- Prove2me | Theorems.Thm_lean_workbook_plus_77072
-- name    : lean_workbook_plus_77072
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/c79a9c19-17ca-4903-95b0-214ccf6e8bb8
-- statement:
--   So, $n^{100}\equiv 1, 3^{100}\mod 1000$ . And also $n^{101}\equiv n\mod 1000\Leftrightarrow n^{100}\equiv 1\mod 1000$ . We need to check that $3^{100}\equiv 1\mod 1000$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77072 :
  (3^100) % 1000 = 1   :=  by sorry
