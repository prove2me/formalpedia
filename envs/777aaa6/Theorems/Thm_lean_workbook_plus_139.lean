-- Prove2me | Theorems.Thm_lean_workbook_plus_139
-- name    : lean_workbook_plus_139
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f54197a5-b236-4a97-b890-9bd0c2265faa
-- statement:
--   If $m$ is a multiple of $n$ , then $m$ can be expressed as $m = nx$ where $x$ is an integer. Since $0$ is an integer, then yes you would consider $0$ a multiple of all naturals.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_139 :
  ∀ m n, m % n = 0 → ∃ x, m = n * x   :=  by sorry
