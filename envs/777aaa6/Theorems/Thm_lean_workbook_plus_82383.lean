-- Prove2me | Theorems.Thm_lean_workbook_plus_82383
-- name    : lean_workbook_plus_82383
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/49f56407-3d63-419f-82e3-ab7926b2ae6b
-- statement:
--   If $ a$ , $ b$ and $ x$ are positive numbers we have that $ 1\ge\dfrac{a}{b}\Leftrightarrow\dfrac{x+a}{x+b}\ge\dfrac{a}{b}$ with equality if and only if $ a=b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82383 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) : 1 ≥ a / b ↔ (x + a) / (x + b) ≥ a / b   :=  by sorry
