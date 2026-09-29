-- Prove2me | Theorems.Thm_lean_workbook_plus_66899
-- name    : lean_workbook_plus_66899
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/d3ce1b19-90f8-4ba5-bb89-20ad256e4739
-- statement:
--   Let $n \equiv 0 \mod a$ for some number $a \ge 2$ . This is true iff $n$ is divisible by $a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66899 (n a : ℕ) (h₁ : 2 ≤ a) : n % a = 0 ↔ a ∣ n   :=  by sorry
