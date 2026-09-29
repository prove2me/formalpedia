-- Prove2me | Theorems.Thm_lean_workbook_plus_63479
-- name    : lean_workbook_plus_63479
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ee1e2888-65a5-4867-b534-9a6483816077
-- statement:
--   Prove that if $x$ and $y$ have the same last digit in base $5$, then $x + y \equiv (x \mod 5) + (y \mod 5) \pmod{5}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63479 (x y : ℕ) (h₁ : x % 5 = y % 5) : (x + y) % 5 = (x % 5 + y % 5) % 5   :=  by sorry
