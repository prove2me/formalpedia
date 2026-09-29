-- Prove2me | Theorems.Thm_lean_workbook_plus_80138
-- name    : lean_workbook_plus_80138
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c876f9bf-d726-4d5e-99ce-d0198fad5f52
-- statement:
--   Prove that $\tan x \tan y \cdot \frac{\tan x + \tan y}{\tan x \tan y - 1} = \frac{\tan^2 x \tan y + \tan x \tan^2 y}{\tan x \tan y - 1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80138  (x y : ℝ) :
  tan x * tan y * (tan x + tan y) / (tan x * tan y - 1) =
    (tan x ^ 2 * tan y + tan x * tan y ^ 2) / (tan x * tan y - 1)   :=  by sorry
