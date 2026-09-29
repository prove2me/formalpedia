-- Prove2me | Theorems.Thm_lean_workbook_plus_71585
-- name    : lean_workbook_plus_71585
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/03cbadbc-b005-4da0-a789-e8ccabb9115a
-- statement:
--   Observe that $ 641 = 5^4 + 2^4$ divides $ A = 5^4\cdot 2^{28} + 2^{32}$ and $ 641 = 5\cdot 2^7 + 1$ divides $ B = (5 \cdot 2^7)^4 - 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71585 : 5^4 + 2^4 ∣ 5^4 * 2^28 + 2^32   :=  by sorry
