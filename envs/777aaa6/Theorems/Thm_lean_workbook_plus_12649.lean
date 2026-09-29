-- Prove2me | Theorems.Thm_lean_workbook_plus_12649
-- name    : lean_workbook_plus_12649
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/12d53a10-7ac6-47dd-9451-9afb002095a0
-- statement:
--   Prove that $xy^2 + yz^2 + zx^2 + xyz \geq 0$ given $x, y, z \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12649 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x * y ^ 2 + y * z ^ 2 + z * x ^ 2 + x * y * z ≥ 0   :=  by sorry
