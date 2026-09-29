-- Prove2me | Theorems.Thm_lean_workbook_plus_16914
-- name    : lean_workbook_plus_16914
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3429fe5c-eef1-41fc-b5ac-418e157e5540
-- statement:
--   Let the 7 consecutive numbers be $x,2x,4x,...,64x$ . Then we have $x+2x+...+64x=127x=254$ and $x=2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16914 (x : ℕ) : x + 2 * x + 4 * x + 8 * x + 16 * x + 32 * x + 64 * x = 254 → x = 2   :=  by sorry
