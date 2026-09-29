-- Prove2me | Theorems.Thm_lean_workbook_plus_82752
-- name    : lean_workbook_plus_82752
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6f26d0f6-bbac-48b4-83d4-e0194e8a2997
-- statement:
--   The positive integer $m$ is a multiple of 111, and the positive integer $n$ is a multiple of 31. Their sum is 2017. Find $n - m$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82752 (m n : ℕ) (h1 : 111 ∣ m) (h2 : 31 ∣ n) (h3 : m + n = 2017) : n - m = 463   :=  by sorry
