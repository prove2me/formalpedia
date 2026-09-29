-- Prove2me | Theorems.Thm_lean_workbook_plus_57902
-- name    : lean_workbook_plus_57902
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/26f3bf29-5143-4a42-954d-e995cb38c184
-- statement:
--   $ x^{10}=1(mod 2) \Leftrightarrow x$ is odd.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57902 : x ^ 10 ≡ 1 [ZMOD 2] ↔ x % 2 = 1   :=  by sorry
