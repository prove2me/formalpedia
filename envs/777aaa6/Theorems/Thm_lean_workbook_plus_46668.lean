-- Prove2me | Theorems.Thm_lean_workbook_plus_46668
-- name    : lean_workbook_plus_46668
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/7b50b2f0-1443-47cb-b93e-a0fccbcf9fe0
-- statement:
--   If $ 3|n - 2$ , then $ n^2 + n + 2\equiv 2\pmod{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46668 : 3 ∣ (n - 2) → n ^ 2 + n + 2 ≡ 2 [ZMOD 3]   :=  by sorry
