-- Prove2me | Theorems.Thm_lean_workbook_plus_59886
-- name    : lean_workbook_plus_59886
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5d9a204f-36b9-4b38-8ab4-d8266eb7debb
-- statement:
--   Prove that $(k-1)k(k+1)$ is divisible by $6$ for $k \ge 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59886 : ∀ k ≥ 3, 6 ∣ (k-1) * k * (k+1)   :=  by sorry
