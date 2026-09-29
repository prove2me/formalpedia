-- Prove2me | Theorems.Thm_lean_workbook_plus_12670
-- name    : lean_workbook_plus_12670
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/96dac8c5-2050-4379-a842-255b891e20ec
-- statement:
--   Let $a,b,c \in [1,2]$ . Prove that $2(ab+bc+ca) \geq a^2+b^2+c^2+a+b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12670 {a b c : ℝ} (ha : a ∈ Set.Icc 1 2) (hb : b ∈ Set.Icc 1 2) (hc : c ∈ Set.Icc 1 2) : 2 * (a * b + b * c + c * a) ≥ a ^ 2 + b ^ 2 + c ^ 2 + a + b + c   :=  by sorry
