-- Prove2me | Theorems.Thm_lean_workbook_plus_55536
-- name    : lean_workbook_plus_55536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/5576cf17-3569-4c85-837f-59204218ac13
-- statement:
--   Prove that $ \dfrac{1}{2}\left(\dfrac{1}{a}+\dfrac{1}{b}+\dfrac{1}{c}\right)\ge \dfrac{1}{a+b}+\dfrac{1}{a+c}+\dfrac{1}{b+c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55536 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / 2) * (1 / a + 1 / b + 1 / c) ≥ 1 / (a + b) + 1 / (a + c) + 1 / (b + c)   :=  by sorry
