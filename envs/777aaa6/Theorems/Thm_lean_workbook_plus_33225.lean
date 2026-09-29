-- Prove2me | Theorems.Thm_lean_workbook_plus_33225
-- name    : lean_workbook_plus_33225
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/b9ff0ba7-550c-42da-9e05-a18d43e39e71
-- statement:
--   Find the necessary and sufficient condition for numbers $a\in\mathbb Z\setminus \{-1,0,1\}$ , $b,c\in\mathbb Z\setminus \{0\}$ , and $d\in\mathbb N\setminus\{0,1\}$ for which $a^n+bn+c$ is divisible by $d$ for each natural number $n.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33225 (a b c d : ℤ) (n : ℕ) : (a^n + b*n + c) % d = 0 ↔ (d ∣ a^n + b*n + c)   :=  by sorry
