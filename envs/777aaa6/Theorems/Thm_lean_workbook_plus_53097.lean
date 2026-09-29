-- Prove2me | Theorems.Thm_lean_workbook_plus_53097
-- name    : lean_workbook_plus_53097
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/c27fc974-d73a-4a04-ad2c-f9cd91a28aec
-- statement:
--   Rearrange and prove the inequality $(x-y)(y-z)(x-z) \geq 0$ for $x \ge y \ge z \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53097 (x y z : ℝ) (hx : x ≥ y) (hy : y ≥ z) (hz : z ≥ 0) : (x - y) * (y - z) * (x - z) ≥ 0   :=  by sorry
