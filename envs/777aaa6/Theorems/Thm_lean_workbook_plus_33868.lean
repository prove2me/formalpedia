-- Prove2me | Theorems.Thm_lean_workbook_plus_33868
-- name    : lean_workbook_plus_33868
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f8a4a48c-607d-441e-a51f-ef24dbb793f2
-- statement:
--   200 choose 100 = $ \binom{200}{100}=\frac{200!}{100!100!}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33868 : Nat.choose 200 100 = 200! / (100! * 100!)   :=  by sorry
